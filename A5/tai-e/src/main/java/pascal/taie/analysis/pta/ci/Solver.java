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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if(!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);
            for(Stmt stmt : method.getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
        // TODO - finish me
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        public Void visit(New stmt){
            workList.addEntry(pointerFlowGraph.getVarPtr(stmt.getLValue()), new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }
        public Void visit(Copy stmt){
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()),pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }
        public Void visit(LoadField stmt){
            if(!stmt.isStatic()){
                return null;
            }
            addPFGEdge(pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()),pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }
        public Void visit(StoreField stmt){
            if(!stmt.isStatic()){
                return null;
            }
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()),pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()));
            return null;
        }
        public Void visit(Invoke stmt){
            if(!stmt.isStatic()){
                return null;
            }
            addReachable(stmt.getMethodRef().resolve());
            for(int i = 0 ; i < stmt.getInvokeExp().getArgCount() ; i++){
                addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getInvokeExp().getArg(i)),pointerFlowGraph.getVarPtr(stmt.getMethodRef().resolve().getIR().getParam(i)));
            }
            if(stmt.getResult() != null){
                for(Var var : stmt.getMethodRef().resolve().getIR().getReturnVars()){
                    addPFGEdge(pointerFlowGraph.getVarPtr(var),pointerFlowGraph.getVarPtr(stmt.getResult()));
                }
            }
            return null;
        }

    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        for(Pointer pointer : pointerFlowGraph.getSuccsOf(source)) {
            if(pointer.equals(target)) return ;
        }
        pointerFlowGraph.addEdge(source, target);
        if(!source.getPointsToSet().isEmpty()){
            workList.addEntry(target,source.getPointsToSet());
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pointsToSet = propagate(pointer,entry.pointsToSet());
            if(pointer instanceof VarPtr varptr){
                for(Obj obj : pointsToSet){
                    for(StoreField storefield : varptr.getVar().getStoreFields()){
                        addPFGEdge(pointerFlowGraph.getVarPtr(storefield.getRValue()),pointerFlowGraph.getInstanceField(obj,storefield.getFieldRef().resolve()));
                    }
                    for(LoadField loadfield : varptr.getVar().getLoadFields()){
                        addPFGEdge(pointerFlowGraph.getInstanceField(obj,loadfield.getFieldRef().resolve()),pointerFlowGraph.getVarPtr(loadfield.getLValue()));
                    }
                    for(StoreArray storearray : varptr.getVar().getStoreArrays()){
                        addPFGEdge(pointerFlowGraph.getVarPtr(storearray.getRValue()),pointerFlowGraph.getArrayIndex(obj));
                    }
                    for(LoadArray loadarray : varptr.getVar().getLoadArrays()){
                        addPFGEdge(pointerFlowGraph.getArrayIndex(obj),pointerFlowGraph.getVarPtr(loadarray.getLValue()));
                    }
                    processCall(varptr.getVar(),obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet newpointsToSet = new PointsToSet();
        for(Obj obj : pointsToSet){
            if(!pointer.getPointsToSet().contains(obj)) newpointsToSet.addObject(obj);
        }
        if(!pointsToSet.isEmpty()){
            for(Obj obj : pointsToSet){
                pointer.getPointsToSet().addObject(obj);
            }
            for(Pointer pointer1 : pointerFlowGraph.getSuccsOf(pointer)){
                workList.addEntry(pointer1,newpointsToSet);
            }
        }
        return newpointsToSet;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for(Invoke invoke : var.getInvokes()){
            if(invoke.isStatic()) continue;
            JMethod method = resolveCallee(recv,invoke);
            workList.addEntry(pointerFlowGraph.getVarPtr(method.getIR().getThis()),new PointsToSet(recv));
            if(!callGraph.contains(method)) {
                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke),invoke,method));
                addReachable(method);
                for(int i = 0 ; i < invoke.getInvokeExp().getArgCount() ; i++){
                    addPFGEdge(pointerFlowGraph.getVarPtr(invoke.getInvokeExp().getArg(i)),pointerFlowGraph.getVarPtr(method.getIR().getParam(i)));
                }
                if(invoke.getLValue() != null) {
                    for (Var var1 : method.getIR().getReturnVars()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(var1), pointerFlowGraph.getVarPtr(invoke.getLValue()));
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
