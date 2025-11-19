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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // Find all reachable statements
        Set<Stmt> visited = new HashSet<>();
        Set<Stmt> reachable = new HashSet<>();
        Queue<Stmt> bfs = new LinkedList<>();
        bfs.add(cfg.getEntry());
        while(!bfs.isEmpty()) {
            Stmt now = bfs.poll();
            if(visited.contains(now)) {
                continue;
            }
            visited.add(now);
            //下面看赋值语句的情况
            if(now instanceof  AssignStmt assignStmt){
                LValue possiblefakevar = assignStmt.getLValue();
                if(hasNoSideEffect(assignStmt.getRValue()) && possiblefakevar instanceof Var &&!liveVars.getOutFact(now).contains((Var)possiblefakevar)){
                    ;
                }
                else reachable.add(now);
                for(Stmt stmt : cfg.getSuccsOf(now)){
                    if(!visited.contains(stmt)){
                        bfs.add(stmt);
                    }
                }
            }
            else if(now instanceof If stmt_if){
                Value condition = ConstantPropagation.evaluate(stmt_if.getCondition(),constants.getInFact(now));
                if(condition.isConstant()){
                    int val =  condition.getConstant();
                    for(Edge<Stmt> edge : cfg.getOutEdgesOf(now)){
                        if((val == 0 && edge.getKind() == Edge.Kind.IF_FALSE) || (val != 0 && edge.getKind() == Edge.Kind.IF_TRUE)){
                            bfs.add(edge.getTarget());
                        }
                    }
                }
                else{
                    for(Stmt stmt : cfg.getSuccsOf(now)){
                        if(!visited.contains(stmt)){
                            bfs.add(stmt);
                        }
                    }
                }
                reachable.add(now);
            }
            else if(now instanceof SwitchStmt switch_Stmt){
                Value condition = ConstantPropagation.evaluate(switch_Stmt.getVar(),constants.getInFact(now));
                if(condition.isConstant()){
                    int val =  condition.getConstant();
                    List<pascal.taie.util.collection.Pair<Integer, Stmt>> caseTargets = switch_Stmt.getCaseTargets();
                    boolean iffind = false;
                    for(Pair<Integer, Stmt> pair : caseTargets){
                        if(pair.first() == val){
                            iffind = true;
                            bfs.add(pair.second());
                        }
                    }
                    if(!iffind){
                        bfs.add(switch_Stmt.getDefaultTarget());
                    }
                }
                else{
                    for(Stmt stmt : cfg.getSuccsOf(now)){
                        if(!visited.contains(stmt)){
                            bfs.add(stmt);
                        }
                    }
                }
                reachable.add(now);
            }
            else{
                reachable.add(now);
                for(Stmt stmt : cfg.getSuccsOf(now)){
                    if(!visited.contains(stmt)){
                        bfs.add(stmt);
                    }
                }
            }
        }
        for (Stmt stmt : cfg.getNodes()) {
            if (!reachable.contains(stmt)) {
                deadCode.add(stmt);
            }
        }
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
