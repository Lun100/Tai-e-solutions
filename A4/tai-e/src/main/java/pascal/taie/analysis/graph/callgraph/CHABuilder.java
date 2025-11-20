/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

import static pascal.taie.analysis.graph.callgraph.CallKind.INTERFACE;


/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> workList = new ArrayDeque<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod currentMethod = workList.poll();
            if (callGraph.reachableMethods.contains(currentMethod)) continue;
            callGraph.addReachableMethod(currentMethod);
            for (Invoke callSite : callGraph.getCallSitesIn(currentMethod)) {
                Set<JMethod> targetMethods = resolve(callSite);
                for (JMethod targetMethod : targetMethods) {
                    CallKind callKind = CallGraphs.getCallKind(callSite);
                    callGraph.addEdge(new Edge<>(callKind, callSite, targetMethod));
                    workList.add(targetMethod);
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> methods = new HashSet<>();
        Subsignature subsignature = callSite.getMethodRef().getSubsignature();
        JClass jclass = callSite.getMethodRef().getDeclaringClass();
        JMethod jmethod = jclass.getDeclaredMethod(subsignature);
        switch(CallGraphs.getCallKind(callSite)){
            case STATIC -> methods.add(jmethod);
            case SPECIAL -> methods.add(dispatch(jclass, subsignature));
            case VIRTUAL -> {
                Queue<JClass> queue = new ArrayDeque<>();
                queue.add(jclass);
                while(!queue.isEmpty()) {
                    JClass jclass1 = queue.poll();
                    methods.add(dispatch(jclass1, subsignature));
                    queue.addAll(hierarchy.getDirectSubclassesOf(jclass1));
                }
            }
            case INTERFACE -> {
                Queue<JClass> queue = new ArrayDeque<>();
                queue.add(jclass);
                while(!queue.isEmpty()) {
                    JClass jclass1 = queue.poll();
                    methods.add(dispatch(jclass1, subsignature));
                    queue.addAll(hierarchy.getDirectSubclassesOf(jclass1));
                    queue.addAll(hierarchy.getDirectImplementorsOf(jclass1));
                    queue.addAll(hierarchy.getDirectSubinterfacesOf(jclass1));
                }
            }
        }
        methods.remove(null);
        return methods;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if(jclass == null) {return null;}
        JMethod jMethod = jclass.getDeclaredMethod(subsignature);
        if(jMethod != null &&  !jMethod.isAbstract()) {return jMethod;}
        else return dispatch(jclass.getSuperClass(), subsignature);
    }
}
