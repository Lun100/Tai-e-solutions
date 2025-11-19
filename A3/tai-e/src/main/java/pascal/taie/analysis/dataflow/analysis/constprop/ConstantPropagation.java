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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;
import java.util.Optional;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact fact = new CPFact();
        Value nac = Value.getNAC();
        for(Var var : cfg.getIR().getParams()){
            if(canHoldInt(var)) fact.update(var,nac);
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for(Var var : fact.keySet()){
            target.update(var,meetValue(fact.get(var),target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me

        if(v1.isNAC() || v2.isNAC()){
            return Value.getNAC();
        }
        if (v1.isUndef()) {
            return v2;
        }
        else if (v2.isUndef()) {
            return v1;
        }
        else if (v1.equals(v2)) {
            return v1;
        }
        else{
            return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact old_out = out.copy();
        out.copyFrom(in);
        if(stmt instanceof DefinitionStmt definitionStmt){
            if(definitionStmt.getLValue() instanceof Var && canHoldInt((Var)definitionStmt.getLValue())){
                out.update((Var)definitionStmt.getLValue(),evaluate(definitionStmt.getRValue(),out));
            }
        }
        return !out.equals(old_out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if(exp instanceof Var){
            return in.get((Var) exp);
        }
        else if(exp instanceof IntLiteral){
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        else if(exp instanceof BinaryExp){
            return evaluateBinaryExp((BinaryExp) exp, in);
        }
        return Value.getNAC();
    }
    public static Value evaluateBinaryExp(BinaryExp exp, CPFact in) {
        Var var1 = exp.getOperand1();
        Var var2 = exp.getOperand2();
        Value v1 = in.get(var1);
        Value v2 = in.get(var2);
        if(canHoldInt(var1) && canHoldInt(var2)){
            if(v1.isNAC() || v2.isNAC()){
                return Value.getNAC();
            }
            else if(v1.isConstant() && v2.isConstant()){
                Value result = Value.getNAC();
                if(exp instanceof ArithmeticExp){
                    result = switch (((ArithmeticExp) exp).getOperator()) {
                        case ADD -> Value.makeConstant(v1.getConstant() + v2.getConstant());
                        case SUB -> Value.makeConstant(v1.getConstant() - v2.getConstant());
                        case MUL -> Value.makeConstant(v1.getConstant() * v2.getConstant());
                        case DIV -> (v2.getConstant() == 0)
                                ? Value.getUndef()
                                : Value.makeConstant(v1.getConstant() / v2.getConstant());

                        case REM -> (v2.getConstant() == 0)
                                ? Value.getUndef()
                                : Value.makeConstant(v1.getConstant() % v2.getConstant());
                    };
                }
                else if(exp instanceof ConditionExp) {
                    result = switch (((ConditionExp) exp).getOperator()) {
                        case EQ -> (v1.getConstant() == v2.getConstant()) ? Value.makeConstant(1) : Value.makeConstant(0);
                        case GE -> (v1.getConstant() >= v2.getConstant()) ? Value.makeConstant(1) : Value.makeConstant(0);
                        case LE -> (v1.getConstant() <= v2.getConstant()) ? Value.makeConstant(1) : Value.makeConstant(0);
                        case GT -> (v1.getConstant() > v2.getConstant()) ? Value.makeConstant(1) : Value.makeConstant(0);
                        case LT -> (v1.getConstant() < v2.getConstant()) ? Value.makeConstant(1) : Value.makeConstant(0);
                        case NE -> (v1.getConstant() != v2.getConstant()) ? Value.makeConstant(1) : Value.makeConstant(0);
                    };
                }
                else if(exp instanceof ShiftExp){
                    result = switch (((ShiftExp) exp).getOperator()){
                        case SHL -> Value.makeConstant(v1.getConstant() << v2.getConstant());
                        case SHR -> Value.makeConstant(v1.getConstant() >> v2.getConstant());
                        case USHR ->  Value.makeConstant(v1.getConstant() >>> v2.getConstant());
                    };
                }
                else if(exp instanceof BitwiseExp){
                    result = switch (((BitwiseExp) exp).getOperator()){
                        case OR ->  Value.makeConstant(v1.getConstant() | v2.getConstant());
                        case AND ->  Value.makeConstant(v1.getConstant() & v2.getConstant());
                        case XOR ->  Value.makeConstant(v1.getConstant() ^ v2.getConstant());
                    };
                }
                return result;
            }
            else{
                return Value.getUndef();
            }
        }
        return Value.getNAC();
    }

}