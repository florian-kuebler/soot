/* Soot - a J*va Optimization Framework
 * Copyright (C) 2003 Ondrej Lhotak
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */

package soot.jimple.toolkits.callgraph;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import soot.AnySubType;
import soot.ArrayType;
import soot.FastHierarchy;
import soot.G;
import soot.NullType;
import soot.PhaseOptions;
import soot.RefType;
import soot.Scene;
import soot.Singletons;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.jimple.SpecialInvokeExpr;
import soot.options.CGOptions;
import soot.toolkits.scalar.Pair;
import soot.util.Chain;
import soot.util.LargeNumberedMap;
import soot.util.NumberedString;
import soot.util.SmallNumberedMap;
import soot.util.queue.ChunkedQueue;

/** Resolves virtual calls.
 * @author Ondrej Lhotak
 * @author Florian Kuebler
 */
public final class VirtualCalls
{ 
	
	public static int counter = 0;
	private CGOptions options = new CGOptions( PhaseOptions.v().getPhaseOptions("cg") );
	
    public VirtualCalls( Singletons.Global g ) { }
    
    public static VirtualCalls v() { return G.v().soot_jimple_toolkits_callgraph_VirtualCalls(); }

    private final LargeNumberedMap<Type, SmallNumberedMap<SootMethod>> typeToVtbl =
        new LargeNumberedMap<Type, SmallNumberedMap<SootMethod>>( Scene.v().getTypeNumberer() );

    public SootMethod resolveSpecial( SpecialInvokeExpr iie, NumberedString subSig, SootMethod container ) {
    	return resolveSpecial(iie, subSig, container, false);
    }
    
    public SootMethod resolveSpecial( SpecialInvokeExpr iie, NumberedString subSig, SootMethod container,
    		boolean appOnly) {
        SootMethod target = iie.getMethod();
        /* cf. JVM spec, invokespecial instruction */
        if( Scene.v().getOrMakeFastHierarchy()
                .canStoreType( container.getDeclaringClass().getType(),
                    target.getDeclaringClass().getType() )
            && container.getDeclaringClass().getType() !=
                target.getDeclaringClass().getType() 
            && !target.getName().equals( "<init>" ) 
            && subSig != sigClinit ) {

            return resolveNonSpecial(
                    container.getDeclaringClass().getSuperclass().getType(),
                    subSig,
                    appOnly);
        } else {
            return target;
        }
    }

    public SootMethod resolveNonSpecial( RefType t, NumberedString subSig) {
    	return resolveNonSpecial(t, subSig, false);
    }
    
    public SootMethod resolveNonSpecial( RefType t, NumberedString subSig,
    		boolean appOnly) {
        SmallNumberedMap<SootMethod> vtbl = typeToVtbl.get( t );
        if( vtbl == null ) {
            typeToVtbl.put( t, vtbl =
                    new SmallNumberedMap<SootMethod>( Scene.v().getMethodNumberer() ) );
        }
        SootMethod ret = vtbl.get( subSig );
        if( ret != null ) return ret;
        SootClass cls = t.getSootClass();
        if (appOnly && cls.isLibraryClass())
        	return null;
        
        SootMethod m = cls.getMethodUnsafe( subSig );
        if( m != null ) {
            if( m.isConcrete() || m.isNative() || m.isPhantom() ) {
                ret = m;
            }
        } else {
            if( cls.hasSuperclass() ) {
                ret = resolveNonSpecial( cls.getSuperclass().getType(), subSig );
            }
        }
        vtbl.put( subSig, ret );
        return ret;
    }

    private final Map<Type,List<Type>> baseToSubTypes = new HashMap<Type,List<Type>>();
    private final Map<Pair<Type, String>, Set<Type>> baseToPossibleSubTypes = new HashMap<Pair<Type,String>, Set<Type>>();

    public void resolve( Type t, Type declaredType, NumberedString subSig,
    		SootMethod container, ChunkedQueue<SootMethod> targets ) {
        resolve(t, declaredType, null, subSig, container, targets);
    }
    
    public void resolve( Type t, Type declaredType, NumberedString subSig,
    		SootMethod container, ChunkedQueue<SootMethod> targets, boolean appOnly ) {
        resolve(t, declaredType, null, subSig, container, targets, appOnly);
    }
    
    public void resolve( Type t, Type declaredType, Type sigType, NumberedString subSig,
    		SootMethod container, ChunkedQueue<SootMethod> targets ) {
    	resolve(t, declaredType, sigType, subSig, container, targets, false);
    }
    
    public void resolve( Type t, Type declaredType, Type sigType, NumberedString subSig,
    		SootMethod container, ChunkedQueue<SootMethod> targets, boolean appOnly ) {
        if( declaredType instanceof ArrayType ) declaredType = RefType.v("java.lang.Object");
        if( sigType instanceof ArrayType ) sigType = RefType.v("java.lang.Object");
        if( t instanceof ArrayType ) t = RefType.v( "java.lang.Object" );
        FastHierarchy fastHierarchy = Scene.v().getOrMakeFastHierarchy();
		if( declaredType != null && !fastHierarchy.canStoreType( t, declaredType ) ) {
            return;
        }
        if( sigType != null && !fastHierarchy.canStoreType( t, sigType ) ) {
            return;
        }
        if( t instanceof RefType ) {
            SootMethod target = resolveNonSpecial( (RefType) t, subSig, appOnly );
            if( target != null ) targets.add( target );
        } else if( t instanceof AnySubType ) {
        	RefType base = ((AnySubType) t).getBase();
        	
        	/*
        	 * Whenever any sub type of a specific type is considered as 
        	 * receiver for a method to call and the base type is an interface, calls to existing methods with matching signature (possible implementation 
        	 * of method to call) are also added. As Javas' subtyping allows contra-variance for return types and co-variance for parameters when overriding 
        	 * a method, these cases are also considered here.
        	 * 
        	 * Example: Classes A, B (B sub type of A), interface I with method public A foo(B b); and a class C with method public B foo(A a) { ... }.
        	 * The extended class hierarchy will contain C as possible implementation of I.
        	 * 
        	 * Since Java has no multiple inheritance call by signature resolution is only activated if the base is an interface.
        	 */
        	if (options.library() == CGOptions.library_signature_resolution && base.getSootClass().isInterface()) {
        		assert(declaredType instanceof RefType);
            	Pair<Type, String> pair = new Pair<Type, String>(base, subSig.getString());
            	Set<Type> types = baseToPossibleSubTypes.get(pair);
            	
            	// if this type and method has been resolved earlier we can just retrieve the previous result.
            	if (types != null) {
            		for(Type st : types) {
            			if (!fastHierarchy.canStoreType( st, declaredType)) {
            				resolve( st, st, sigType, subSig, container, targets, appOnly);
            			} else {
            				resolve (st, declaredType, sigType, subSig, container, targets, appOnly);
            			}
            		}
            		return;
            	}
            	
            	baseToPossibleSubTypes.put(pair, types = new HashSet<Type>());
            	
            	//TODO: use base or declaredClass?
            	SootMethod m = base.getSootClass().getMethod(subSig);
            	
            	Chain<SootClass> classes = Scene.v().getClasses();
            	for(SootClass sc : classes) {
            		for(SootMethod sm : sc.getMethods()) {
            			if (sm.isConcrete() || sm.isNative()) {
            				if (check(sm, m.getName(), m.getReturnType(), m.getParameterTypes(), fastHierarchy)) {
        						Type st = sc.getType();
        						if (!fastHierarchy.canStoreType(st, declaredType)) {
        							// final classes can not be extended and therefore not used in library client
        							if (!sc.isFinal()) {
        								NumberedString newSubSig = sm.getNumberedSubSignature();
										resolve( st, st, sigType, newSubSig, container, targets, appOnly);
        								types.add(st);
        							}
        						} else {
        							resolve (st, declaredType, sigType, subSig, container, targets, appOnly);
        							types.add(st);
        						}
        					}
        				}
            		}
            	}
        	} else {
	            List<Type> subTypes = baseToSubTypes.get(base);
	            if( subTypes != null ) {
	            	for (Type st : subTypes) {
	            		resolve(st, declaredType, sigType, subSig, container, targets, appOnly);
	            	}
	                return;
	            }
	
	            baseToSubTypes.put(base, subTypes = new ArrayList<Type>() );
	
	            subTypes.add(base);
	
	            LinkedList<SootClass> worklist = new LinkedList<SootClass>();
	            HashSet<SootClass> workset = new HashSet<SootClass>();
	            FastHierarchy fh = fastHierarchy;
	            SootClass cl = base.getSootClass();
	            
	            workset.add(cl);
	            worklist.add(cl);
	            
	            while (!worklist.isEmpty()) {
	            	cl = worklist.removeFirst();
	                if( cl.isInterface() ) {
	                	for (SootClass c : fh.getAllImplementersOfInterface(cl))
	                		if (workset.add(c))
	                			worklist.add(c);
	                } else {
	                	if( cl.isConcrete() ) {
	                        resolve(cl.getType(), declaredType, sigType, subSig, container, targets, appOnly);
	                        subTypes.add(cl.getType());
	                    }
	                    for (SootClass c : fh.getSubclassesOf(cl))
	                    	if (workset.add(c))
	                    		worklist.add(c);
	                }
	            }
	        }
        } else if (t instanceof NullType) {
        } else {
            throw new RuntimeException("oops "+t );
        }
    }
    
    public final NumberedString sigClinit =
        Scene.v().getSubSigNumberer().findOrAdd("void <clinit>()");
    public final NumberedString sigStart =
        Scene.v().getSubSigNumberer().findOrAdd("void start()");
    public final NumberedString sigRun =
        Scene.v().getSubSigNumberer().findOrAdd("void run()");
    
    //TODO: rename me
    private boolean check(SootMethod sm, String declaredName, Type declaredReturnType, List<Type> declaredParamTypes, FastHierarchy fastHierarchy) {
		// method name has to match
		if (!sm.getName().equals(declaredName)) return false;
		
		// the return type has to be a the declared return type or a sub type of it
		if (!fastHierarchy.canStoreType(sm.getReturnType(), declaredReturnType)) return false;
		List<Type> paramTypes = sm.getParameterTypes();
		
		// method parameters have to match to the declared ones (same type or super type).
		if (declaredParamTypes.size() != paramTypes.size()) return false;
		
		for (int i = 0; i < paramTypes.size(); i++) {
			if (!fastHierarchy.canStoreType(declaredParamTypes.get(i), paramTypes.get(i))) {
				return false;
			}
		}
		
		return true;
    }
}


