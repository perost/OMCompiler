/*
 * This file is part of OpenModelica.
 *
 * Copyright (c) 1998-2014, Open Source Modelica Consortium (OSMC),
 * c/o Linköpings universitet, Department of Computer and Information Science,
 * SE-58183 Linköping, Sweden.
 *
 * All rights reserved.
 *
 * THIS PROGRAM IS PROVIDED UNDER THE TERMS OF GPL VERSION 3 LICENSE OR
 * THIS OSMC PUBLIC LICENSE (OSMC-PL) VERSION 1.2.
 * ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES
 * RECIPIENT'S ACCEPTANCE OF THE OSMC PUBLIC LICENSE OR THE GPL VERSION 3,
 * ACCORDING TO RECIPIENTS CHOICE.
 *
 * The OpenModelica software and the Open Source Modelica
 * Consortium (OSMC) Public License (OSMC-PL) are obtained
 * from OSMC, either from the above address,
 * from the URLs: http://www.ida.liu.se/projects/OpenModelica or
 * http://www.openmodelica.org, and in the OpenModelica distribution.
 * GNU version 3 is obtained from: http://www.gnu.org/copyleft/gpl.html.
 *
 * This program is distributed WITHOUT ANY WARRANTY; without
 * even the implied warranty of  MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY SET FORTH
 * IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS OF OSMC-PL.
 *
 * See the full OSMC Public License conditions for more details.
 *
 */

encapsulated package InstSection
" file:        InstSection.mo
  package:     InstSection
  description: Model instantiation


  This module is responsible for instantiation of Modelica equation
  and algorithm sections (including connect equations)."

public import Absyn;
public import ClassInf;
public import Connect;
public import DAE;
public import FCore;
public import FGraph;
public import InnerOuter;
public import Prefix;
public import SCode;

protected import Algorithm;
protected import Ceval;
protected import ComponentReference;
protected import Config;
protected import ConnectUtil;
protected import DAEUtil;
protected import Debug;
protected import Dump;
protected import ElementSource;
protected import Error;
protected import Expression;
protected import ExpressionDump;
protected import ExpressionSimplify;
protected import ExpressionSimplifyTypes;
protected import Flags;
protected import Inst;
protected import InstDAE;
protected import InstFunction;
protected import InstTypes;
protected import InstUtil;
protected import NFInstUtil;
protected import List;
protected import Lookup;
protected import Patternm;
protected import PrefixUtil;
protected import Static;
protected import Types;
protected import Util;
protected import Values;
protected import ValuesUtil;
protected import System;
protected import ErrorExt;
protected import SCodeDump;
protected import DAEDump;

protected type Ident = DAE.Ident "an identifier";
protected type InstanceHierarchy = InnerOuter.InstHierarchy "an instance hierarchy";
protected constant Boolean alwaysUnroll = true;

public function instEquation
"author: LS, ELN

  Instantiates an equation by calling
  instEquationCommon with Inital set
  to NON_INITIAL."
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input SCode.Equation inEquation;
  input Boolean inImpl;
  input Boolean unrollForLoops "Unused, to comply with Inst.instList interface.";
  output FCore.Cache outCache;
  output FCore.Graph outEnv;
  output InnerOuter.InstHierarchy outIH;
  output DAE.DAElist outDae;
  output ClassInf.State outState;
protected
  SCode.EEquation eq;
algorithm
  SCode.EQUATION(eEquation = eq) := inEquation;
  (outCache, outEnv, outIH, outDae, outState) :=
    instEquationCommon(inCache, inEnv, inIH, inPrefix, inState, eq,
      SCode.NON_INITIAL(), inImpl);
end instEquation;

protected function instEEquation
  "Instantiation of EEquation, used in for loops and if-equations."
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input SCode.EEquation inEEquation;
  input Boolean inImpl;
  input Boolean unrollForLoops "Unused, to comply with Inst.instList interface.";
  output FCore.Cache outCache;
  output FCore.Graph outEnv;
  output InnerOuter.InstHierarchy outIH;
  output DAE.DAElist outDae;
  output ClassInf.State outState;
algorithm
  (outCache, outEnv, outIH, outDae, outState) :=
    instEquationCommon(inCache, inEnv, inIH, inPrefix, inState, inEEquation,
      SCode.NON_INITIAL(), inImpl);
end instEEquation;

public function instInitialEquation
"author: LS, ELN
  Instantiates initial equation by calling inst_equation_common with Inital
  set to INITIAL."
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input SCode.Equation inEquation;
  input Boolean inImpl;
  input Boolean unrollForLoops "Unused, to comply with Inst.instList interface.";
  output FCore.Cache outCache;
  output FCore.Graph outEnv;
  output InnerOuter.InstHierarchy outIH;
  output DAE.DAElist outDae;
  output ClassInf.State outState;
protected
  SCode.EEquation eq;
algorithm
  SCode.EQUATION(eEquation = eq) := inEquation;
  (outCache, outEnv, outIH, outDae, outState) :=
    instEquationCommon(inCache, inEnv, inIH, inPrefix, inState, eq,
      SCode.INITIAL(), inImpl);
end instInitialEquation;

protected function instEInitialEquation
  "Instantiates initial EEquation used in for loops and if equations "
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input SCode.EEquation inEEquation;
  input Boolean inImpl;
  input Boolean unrollForLoops "Unused, to comply with Inst.instList interface.";
  output FCore.Cache outCache;
  output FCore.Graph outEnv;
  output InnerOuter.InstHierarchy outIH;
  output DAE.DAElist outDae;
  output ClassInf.State outState;
algorithm
  (outCache, outEnv, outIH, outDae, outState) :=
    instEquationCommon(inCache, inEnv, inIH, inPrefix, inState, inEEquation,
      SCode.INITIAL(), inImpl);
end instEInitialEquation;

protected function instEquationCommon
  "The DAE output of the translation contains equations which
  in most cases directly corresponds to equations in the source.
  Some of them are also generated from `connect\' clauses.

  This function takes an equation from the source and generates DAE
  equations and connection sets."
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input SCode.EEquation inEEquation;
  input SCode.Initial inInitial;
  input Boolean inImpl;
  output FCore.Cache outCache;
  output FCore.Graph outEnv;
  output InnerOuter.InstHierarchy outIH;
  output DAE.DAElist outDae;
  output ClassInf.State outState;
protected
  Integer errorCount = Error.getNumErrorMessages();
algorithm
  _ := matchcontinue()
    local
      String s;
      ClassInf.State state;

    case ()
      algorithm
        state := ClassInf.trans(inState,ClassInf.FOUND_EQUATION());
        (outCache, outEnv, outIH, outDae, outState) :=
          instEquationCommonWork(inCache, inEnv, inIH, inPrefix, state,
            inEEquation, inInitial, inImpl, DAE.FLATTEN(inEEquation, NONE()));
        outDae := DAEUtil.traverseDAE(outDae, DAE.AvlTreePathFunction.Tree.EMPTY(),
          Expression.traverseSubexpressionsHelper,
          (ExpressionSimplify.simplifyWork, ExpressionSimplifyTypes.optionSimplifyOnly));
      then
        ();

    case ()
      algorithm
        failure(_ := ClassInf.trans(inState,ClassInf.FOUND_EQUATION()));
        s := ClassInf.printStateStr(inState);
        Error.addSourceMessage(Error.EQUATION_TRANSITION_FAILURE, {s}, SCode.equationFileInfo(inEEquation));
      then
        fail();

    // We only want to print a generic error message if no other error message was printed
    // Providing two error messages for the same error is confusing (but better than none)
    else
      algorithm
        true := errorCount == Error.getNumErrorMessages();
        s := "\n" + SCodeDump.equationStr(inEEquation);
        Error.addSourceMessage(Error.EQUATION_GENERIC_FAILURE, {s}, SCode.equationFileInfo(inEEquation));
      then
        fail();

  end matchcontinue;
end instEquationCommon;

protected function instEquationCommonWork
  "The DAE output of the translation contains equations which in most cases
   directly corresponds to equations in the source. Some of them are also
   generated from connect clauses.

   This function takes an equation from the source and generates DAE equations
   and connection sets."
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input SCode.EEquation inEEquation;
  input SCode.Initial inInitial;
  input Boolean inImpl;
  input DAE.SymbolicOperation inFlattenOp;
  output FCore.Cache outCache = inCache;
  output FCore.Graph outEnv = inEnv;
  output InnerOuter.InstHierarchy outIH = inIH;
  output DAE.DAElist outDae;
  output ClassInf.State outState;
algorithm
  (outDae, outState) := matchcontinue inEEquation
    local
      Absyn.ComponentRef lhs_acr, rhs_acr;
      SourceInfo info;
      Absyn.Exp lhs_aexp, rhs_aexp, range_aexp;
      SCode.Comment comment;
      DAE.Exp lhs_exp, rhs_exp, exp, cond_exp, msg_exp, level_exp, cr_exp;
      DAE.Properties lhs_prop, rhs_prop, prop, cr_prop;
      DAE.ElementSource source;
      list<DAE.Exp> expl;
      list<DAE.Properties> props;
      DAE.Const c;
      Values.Value val;
      Integer idx;
      list<SCode.EEquation> eql, else_branch;
      list<list<SCode.EEquation>> branches, rest_branches;
      list<list<DAE.Element>> ell;
      list<DAE.Element> el, el2;
      list<DAE.ComponentRef> crefs1, crefs2;
      Option<DAE.Element> else_when;
      list<tuple<Absyn.ComponentRef, Integer>> iter_crefs;
      DAE.Type ty;
      FCore.Graph env;
      Values.Value val;
      DAE.ComponentRef cr;
      Boolean branch_selected;

    // Connect equations.
    case SCode.EQ_CONNECT(crefLeft = lhs_acr, crefRight = rhs_acr, info = info)
      algorithm
        source := makeEqSource(info, inEnv, inPrefix, inFlattenOp);
        (outCache, outEnv, outIH, outDae) :=
          instConnect(outCache, outEnv, outIH, inPrefix, lhs_acr,
            rhs_acr, inImpl, info, source);
        outState := instEquationCommonCiTrans(inState, inInitial);
      then
        (outDae, outState);

    // Equality equations.
    case SCode.EQ_EQUALS(expLeft = lhs_aexp, expRight = rhs_aexp, info = info,
        comment = comment)
      algorithm
        // Check that the equation is valid if the lhs is a tuple.
        checkTupleCallEquationMessage(lhs_aexp, rhs_aexp, info);

        (outCache, lhs_exp, lhs_prop) :=
          Static.elabExp(inCache, inEnv, lhs_aexp, inImpl, NONE(), true, inPrefix, info);
        (outCache, rhs_exp, rhs_prop) :=
          Static.elabExp(inCache, inEnv, rhs_aexp, inImpl, NONE(), true, inPrefix, info);

        (outCache, lhs_exp, lhs_prop) :=
          Ceval.cevalIfConstant(outCache, inEnv, lhs_exp, lhs_prop, inImpl, info);
        (outCache, rhs_exp, rhs_prop) :=
          Ceval.cevalIfConstant(outCache, inEnv, rhs_exp, rhs_prop, inImpl, info);

        (outCache, lhs_exp, rhs_exp, lhs_prop) :=
          condenseArrayEquation(outCache, inEnv, lhs_aexp, rhs_aexp, lhs_exp,
            rhs_exp, lhs_prop, rhs_prop, inImpl, inPrefix, info);

        (outCache, lhs_exp) := PrefixUtil.prefixExp(outCache, inEnv, inIH, lhs_exp, inPrefix);
        (outCache, rhs_exp) := PrefixUtil.prefixExp(outCache, inEnv, inIH, rhs_exp, inPrefix);

        // Set the source of this element.
        source := makeEqSource(info, inEnv, inPrefix, inFlattenOp);
        source := ElementSource.addCommentToSource(source, SOME(comment));

        // Check that the lhs and rhs get along.
        outDae := instEqEquation(lhs_exp, lhs_prop, rhs_exp, rhs_prop, source, inInitial, inImpl);
        outState := instEquationCommonCiTrans(inState, inInitial);
      then
        (outDae, outState);

    case SCode.EQ_IF(thenBranch = branches, elseBranch = else_branch, info = info)
      algorithm
        // Elaborate all of the conditions.
        (outCache, expl, props) := Static.elabExpList(outCache, outEnv,
          inEEquation.condition, inImpl, NONE(), true, inPrefix, info);

        // Check that all conditions are Boolean.
        prop := Types.propsAnd(props);
        checkIfConditionTypes(prop, inEEquation.condition, props, info);

        // Try to select one of the branches.
        try
          rest_branches := branches;
          eql := else_branch;

          // Go through each condition and select the first branch whose
          // condition is a parameter expression evaluating to true. If a
          // non-parameter expression is encountered this will fail and fall
          // back to instantiating the whole if equation below. If all
          // conditions evaluate to false the else branch will be selected.
          for cond in expl loop
            DAE.PROP(constFlag = c) :: props := props;
            true := Types.isParameterOrConstant(c);

            (outCache, val) := Ceval.ceval(outCache, outEnv, cond, inImpl,
                NONE(), Absyn.NO_MSG(), 0);
            true := checkIfConditionBinding(val, info);

            if ValuesUtil.valueBool(val) then
              eql := listHead(rest_branches);
              break;
            end if;

            rest_branches := listRest(rest_branches);
          end for;

          // A branch was selected, instantiate it.
          (outCache, outEnv, outIH, outDae, outState) :=
            Inst.instList(outCache, inEnv, inIH, inPrefix, inState,
              if SCode.isInitial(inInitial) then instEInitialEquation else instEEquation,
              eql, inImpl, alwaysUnroll);
        else
          (outCache, expl) := PrefixUtil.prefixExpList(outCache, inEnv, inIH, expl, inPrefix);

          // Set the source of this element.
          source := makeEqSource(info, inEnv, inPrefix, inFlattenOp);

          // Instantiate all branches.
          if SCode.isInitial(inInitial) then
            (outCache, outEnv, outIH, outState, ell) :=
              instInitialIfEqBranches(outCache, inEnv, inIH, inPrefix, inState, branches, inImpl);
            (outCache, outEnv, outIH, outState, el) :=
              instInitialIfEqBranch(outCache, outEnv, outIH, inPrefix, outState, else_branch, inImpl);

            outDae := DAE.DAE({DAE.INITIAL_IF_EQUATION(expl, ell, el, source)});
          else
            (outCache, outEnv, outIH, outState, ell) :=
              instIfEqBranches(outCache, inEnv, inIH, inPrefix, inState, branches, inImpl);
            (outCache, outEnv, outIH, outState, el) :=
              instIfEqBranch(outCache, outEnv, outIH, inPrefix, outState, else_branch, inImpl);

            outDae := DAE.DAE({DAE.IF_EQUATION(expl, ell, el, source)});
          end if;
        end try;
      then
        (outDae, outState);

    case SCode.EQ_WHEN(info = info)
      algorithm
        if SCode.isInitial(inInitial) then
          Error.addSourceMessageAndFail(Error.INITIAL_WHEN, {}, info);
        end if;

        (outCache, outEnv, outIH, cond_exp, el) :=
          instWhenEqBranch(inCache, inEnv, inIH, inPrefix, inState,
            (inEEquation.condition, inEEquation.eEquationLst), inImpl,
            alwaysUnroll, info);

        // Set the source of this element.
        source := makeEqSource(info, inEnv, inPrefix, inFlattenOp);

        else_when := NONE();
        for branch in listReverse(inEEquation.elseBranches) loop
          (outCache, outEnv, outIH, exp, el2) :=
            instWhenEqBranch(outCache, outEnv, outIH, inPrefix, inState,
              branch, inImpl, alwaysUnroll, info);
          else_when := SOME(DAE.WHEN_EQUATION(exp, el2, else_when, source));
        end for;

        outState := instEquationCommonCiTrans(inState, inInitial);
        outDae := DAE.DAE({DAE.WHEN_EQUATION(cond_exp, el, else_when, source)});
      then
        (outDae, outState);

    case SCode.EQ_FOR(info = info)
      algorithm
        // Check if we have an explicit range, and use it if that's the case.
        // Otherwise, try to deduce the implicit range based on how the iterator is used.
        if isSome(inEEquation.range) then
          SOME(range_aexp) := inEEquation.range;

          // Elaborate the range.
          (outCache, exp, DAE.PROP(type_ = DAE.T_ARRAY(ty = ty), constFlag = c), _) :=
            Static.elabExp(outCache, inEnv, range_aexp, inImpl, NONE(), true, inPrefix, info);
        else
          iter_crefs := SCode.findIteratorIndexedCrefsInEEquations(
            inEEquation.eEquationLst, inEEquation.index);
          (exp, DAE.PROP(type_ = DAE.T_ARRAY(ty = ty), constFlag = c), outCache) :=
            Static.deduceIterationRange(inEEquation.index, iter_crefs, inEnv, outCache, info);

          // Ceval below should not fail on our generated range, but just in case...
          range_aexp := Absyn.STRING("Internal error: generated implicit range could not be evaluated.");
        end if;

        // Add the iterator to the environment.
        env := addForLoopScope(inEnv, inEEquation.index, ty, SCode.VAR(), SOME(c));

        // Try to constant evaluate the range.
        try
          (outCache, val) := Ceval.ceval(outCache, inEnv, exp, inImpl, NONE(), Absyn.NO_MSG(), 0);
        else
          // Evaluation failed, which is normally an error since the range
          // should be a parameter expression. If we're doing checkModel we
          // allow it though, and use {1} as range to check that the loop can be
          // instantiated.
          if Flags.getConfigBool(Flags.CHECK_MODEL) then
            val := Values.ARRAY({Values.INTEGER(1)}, {1});
          else
            Error.addSourceMessageAndFail(Error.NON_PARAMETER_ITERATOR_RANGE,
              {Dump.printExpStr(range_aexp)}, info);
          end if;
        end try;

        (outCache, outDae) := unroll(outCache, env, inIH,
           inPrefix, inState, inEEquation.index, ty, val,
           inEEquation.eEquationLst, inInitial, inImpl);
        outState := instEquationCommonCiTrans(inState, inInitial);
      then
        (outDae, outState);

    case SCode.EQ_ASSERT(info = info)
      algorithm
        (outCache, cond_exp) := instOperatorArg(outCache, inEnv, inIH, inPrefix,
            inEEquation.condition, inImpl, DAE.T_BOOL_DEFAULT, "assert", "condition", 1, info);
        (outCache, msg_exp) := instOperatorArg(outCache, inEnv, inIH, inPrefix,
            inEEquation.message, inImpl, DAE.T_STRING_DEFAULT, "assert", "message", 2, info);
        (outCache, level_exp) := instOperatorArg(outCache, inEnv, inIH, inPrefix,
            inEEquation.level, inImpl, DAE.T_ASSERTIONLEVEL, "assert", "level", 3, info);

        source := makeEqSource(info, inEnv, inPrefix, inFlattenOp);
        outDae := DAE.DAE({DAE.ASSERT(cond_exp, msg_exp, level_exp, source)});
      then
        (outDae, inState);

    case SCode.EQ_TERMINATE(info = info)
      algorithm
        (outCache, msg_exp) := instOperatorArg(outCache, inEnv, inIH, inPrefix,
            inEEquation.message, inImpl, DAE.T_STRING_DEFAULT, "terminate", "message", 1, info);

        source := makeEqSource(info, inEnv, inPrefix, inFlattenOp);
        outDae := DAE.DAE({DAE.TERMINATE(msg_exp, source)});
      then
        (outDae, inState);

    case SCode.EQ_REINIT(info = info)
      algorithm
        // Elaborate the cref.
        (outCache, cr_exp as DAE.CREF(cr, ty), cr_prop, _) :=
          Static.elabCrefNoEval(outCache, inEnv, inEEquation.cref, inImpl, false, inPrefix, info);
        true := checkReinitType(ty, cr_prop, cr, info);

        // Elaborate the reinit expression.
        (outCache, exp, prop) :=
          Static.elabExp(outCache, inEnv, inEEquation.expReinit, inImpl, NONE(), true, inPrefix, info);
        (outCache, exp, prop) :=
          Ceval.cevalIfConstant(outCache, inEnv, exp, prop, inImpl, info);

        // Check that the cref and the expression have matching types.
        exp := Types.matchProp(exp, prop, cr_prop, true);

        (outCache, cr_exp, exp, cr_prop) := condenseArrayEquation(outCache,
          inEnv, Absyn.CREF(inEEquation.cref), inEEquation.expReinit, cr_exp,
          exp, cr_prop, prop, inImpl, inPrefix, info);
        (outCache, cr_exp) := PrefixUtil.prefixExp(outCache, inEnv, inIH, cr_exp, inPrefix);
        (outCache, exp) := PrefixUtil.prefixExp(outCache, inEnv, inIH, exp, inPrefix);

        source := makeEqSource(info, inEnv, inPrefix, inFlattenOp);

        DAE.DAE(el) := instEqEquation(cr_exp, cr_prop, exp, prop, source, inInitial, inImpl);
        el := list(makeDAEArrayEqToReinitForm(e) for e in el);
        outDae := DAE.DAE(el);
      then
        (outDae, inState);

    case SCode.EQ_NORETCALL(info = info)
      algorithm
        (outCache, exp) := Static.elabExp(inCache, inEnv, inEEquation.exp,
          inImpl, NONE(), false, inPrefix, info);
        // This is probably an external function call that the user wants to
        // evaluate at runtime, so don't ceval it.
        (outCache, exp) := PrefixUtil.prefixExp(outCache, inEnv, inIH, exp, inPrefix);

        source := makeEqSource(info, inEnv, inPrefix, inFlattenOp);
        outDae := instEquationNoRetCallVectorization(exp, inInitial, source);
        outState := inState;
      then
        (outDae, outState);

    else
      algorithm
        true := Flags.isSet(Flags.FAILTRACE);
        Debug.trace("- InstSection.instEquationCommonWork failed for eqn: ");
        Debug.traceln(SCodeDump.equationStr(inEEquation) + " in scope: " +
            FGraph.getGraphNameStr(inEnv));
      then
        fail();

  end matchcontinue;
end instEquationCommonWork;

protected function makeEqSource
  input Absyn.Info inInfo;
  input FCore.Graph inEnv;
  input Prefix.Prefix inPrefix;
  input DAE.SymbolicOperation inFlattenOp;
  output DAE.ElementSource outSource;
algorithm
  outSource := ElementSource.createElementSource(inInfo, FGraph.getScopePath(inEnv), inPrefix);
  outSource := ElementSource.addSymbolicTransformation(outSource, inFlattenOp);
end makeEqSource;

protected function checkIfConditionTypes
  "Checks that all conditions in an if-equation are Boolean."
  input DAE.Properties inAccumProp;
  input list<Absyn.Exp> inConditions;
  input list<DAE.Properties> inProperties;
  input SourceInfo inInfo;
algorithm
  _ := match inAccumProp
    local
      list<DAE.Properties> props;
      DAE.Type ty;
      String exp_str, ty_str;

    // Boolean type, ok.
    case DAE.PROP(type_ = DAE.T_BOOL()) then ();

    // Any other type, find the offending condition and print an error.
    else
      algorithm
        props := inProperties;

        for cond in inConditions loop
          DAE.PROP(type_ = ty) :: props := props;

          if not Types.isScalarBoolean(ty) then
            exp_str := Dump.printExpStr(cond);
            ty_str := Types.unparseTypeNoAttr(ty);
            Error.addSourceMessageAndFail(Error.IF_CONDITION_TYPE_ERROR,
              {exp_str, ty_str}, inInfo);
          end if;
        end for;

        Error.addInternalError("InstSection.checkIfConditionTypes failed to find non-Boolean condition.", inInfo);
      then
        fail();

  end match;
end checkIfConditionTypes;

protected function checkIfConditionBinding
  "Checks that the condition of an if-branch has a binding."
  input Values.Value inValues;
  input SourceInfo inInfo;
  output Boolean outHasBindings;
protected
  Option<Values.Value> empty_val;
  String scope, name;
algorithm
  empty_val := ValuesUtil.containsEmpty(inValues);

  if isSome(empty_val) then
    SOME(Values.EMPTY(scope = scope, name = name)) := empty_val;
    Error.addSourceMessage(Error.NO_CONSTANT_BINDING, {name, scope}, inInfo);
    outHasBindings := false;
  else
    outHasBindings := true;
  end if;
end checkIfConditionBinding;

protected function instOperatorArg
  "Helper function to instEquationCommonWork. Elaborates and type checks an
   argument for some builtin operators, like assert and terminate."
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input Absyn.Exp inArg;
  input Boolean inImpl;
  input DAE.Type inExpectedType;
  input String inOperatorName;
  input String inArgName;
  input Integer inArgIndex;
  input SourceInfo inInfo;
  output FCore.Cache outCache;
  output DAE.Exp outArg;
protected
  DAE.Properties props;
  DAE.Type ty;
algorithm
  (outCache, outArg, props) :=
    Static.elabExp(inCache, inEnv, inArg, inImpl, NONE(), true, inPrefix, inInfo);
  ty := Types.getPropType(props);

  if not Types.subtype(ty, inExpectedType) then
    Error.addSourceMessageAndFail(Error.ARG_TYPE_MISMATCH,
      {intString(inArgIndex), inOperatorName, inArgName,
       Dump.printExpStr(inArg), Types.unparseTypeNoAttr(ty),
       Types.unparseType(inExpectedType)}, inInfo);
  end if;

  (outCache, outArg) :=
    Ceval.cevalIfConstant(outCache, inEnv, outArg, props, inImpl, inInfo);
  (outCache, outArg) :=
    PrefixUtil.prefixExp(outCache, inEnv, inIH, outArg, inPrefix);
end instOperatorArg;

protected function checkReinitType
  "Checks that the base type of the given type is Real, otherwise it prints an
   error message that the first argument to reinit must be a subtype of Real."
  input DAE.Type inType;
  input DAE.Properties inProperties;
  input DAE.ComponentRef inCref;
  input SourceInfo inInfo;
  output Boolean outSucceeded;
algorithm
  outSucceeded := matchcontinue inProperties
    local
      DAE.Type ty;
      String cref_str, ty_str, cnst_str;
      DAE.Const cnst;

    case _
      equation
        ty = Types.arrayElementType(inType);
        false = Types.isReal(ty);
        cref_str = ComponentReference.printComponentRefStr(inCref);
        ty_str = Types.unparseType(ty);
        Error.addSourceMessage(Error.REINIT_MUST_BE_REAL,
          {cref_str, ty_str}, inInfo);
      then
        false;

    case DAE.PROP(constFlag = cnst)
      equation
        false = Types.isVar(cnst);
        cnst_str = Types.unparseConst(cnst);
        cref_str = ComponentReference.printComponentRefStr(inCref);
        Error.addSourceMessage(Error.REINIT_MUST_BE_VAR,
          {cref_str, cnst_str}, inInfo);
      then
        false;

    else true;

  end matchcontinue;
end checkReinitType;

protected function checkTupleCallEquationMessage
  "Checks that if a tuple is used on the left side of an equation, then it
   must consist only of component references and the right side must be a
   function call."
  input Absyn.Exp left;
  input Absyn.Exp right;
  input SourceInfo info;
algorithm
  _ := match (left, right)
    local
      list<Absyn.Exp> crefs;
      String left_str, right_str;

    case (Absyn.TUPLE(crefs), Absyn.CALL())
      algorithm
        if not List.all(crefs, Absyn.isCref) then
          left_str := Dump.printExpStr(left);
          right_str := Dump.printExpStr(right);
          Error.addSourceMessageAndFail(Error.TUPLE_ASSIGN_CREFS_ONLY,
            {left_str + " = " + right_str + ";"}, info);
        end if;
      then
        ();

    case (Absyn.TUPLE(), _)
      algorithm
        left_str := Dump.printExpStr(left);
        right_str := Dump.printExpStr(right);
        Error.addSourceMessage(Error.TUPLE_ASSIGN_FUNCALL_ONLY,
          {left_str + " = " + right_str + ";"}, info);
      then
        fail();

    else ();
  end match;
end checkTupleCallEquationMessage;

protected function instEquationNoRetCallVectorization
  "Creates DAE for NORETCALLs and also performs vectorization if needed."
  input DAE.Exp exp;
  input SCode.Initial initial_;
  input DAE.ElementSource source "the origin of the element";
  output DAE.DAElist dae;
algorithm
  dae := match initial_
    case SCode.NON_INITIAL() then DAE.DAE({DAE.NORETCALL(exp, source)});
    case SCode.INITIAL() then DAE.DAE({DAE.INITIAL_NORETCALL(exp, source)});
  end match;
end instEquationNoRetCallVectorization;

protected function makeDAEArrayEqToReinitForm
  "Function for transforming DAE equations into DAE.REINIT form,
   used by instEquationCommon."
  input DAE.Element inEq;
  output DAE.Element outEqn;
algorithm
  outEqn := match inEq
    local
      DAE.ComponentRef cr1, cr2;
      DAE.Exp e2, e;
      DAE.Type t;
      DAE.ElementSource source "the origin of the element";

    case DAE.EQUATION(DAE.CREF(componentRef=cr1), e, source)
      then DAE.REINIT(cr1, e, source);

    case DAE.DEFINE(cr1, e, source)
      then DAE.REINIT(cr1, e, source);

    case DAE.EQUEQUATION(cr1, cr2, source)
      algorithm
        t := ComponentReference.crefLastType(cr2);
        e2 := Expression.makeCrefExp(cr2, t);
      then
        DAE.REINIT(cr1, e2, source);

    case DAE.ARRAY_EQUATION(exp = DAE.CREF(componentRef = cr1), array = e, source = source)
      then DAE.REINIT(cr1, e, source);

    else
      algorithm
        true := Flags.isSet(Flags.FAILTRACE);
        Debug.traceln("Failure in: makeDAEArrayEqToReinitForm");
      then
        fail();

  end match;
end makeDAEArrayEqToReinitForm;

protected function condenseArrayEquation "This function transforms makes the two sides of an array equation
into its condensed form. By default, most array variables are vectorized,
i.e. v becomes {v[1],v[2],..,v[n]}. But for array equations containing function calls this is not wanted.
This function detect this case and elaborates expressions without vectorization."
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input Absyn.Exp ie1;
  input Absyn.Exp ie2;
  input DAE.Exp elabedE1;
  input DAE.Exp elabedE2;
  input DAE.Properties iprop "To determine if array equation";
  input DAE.Properties iprop2 "To determine if array equation";
  input Boolean impl;
  input Prefix.Prefix inPrefix;
  input SourceInfo info;
  output FCore.Cache outCache;
  output DAE.Exp outE1;
  output DAE.Exp outE2;
  output DAE.Properties oprop "If we have an expandable tuple";
algorithm
  (outCache,outE1,outE2,oprop) := matchcontinue(inCache,inEnv,ie1,ie2,elabedE1,elabedE2,iprop,iprop2,impl,inPrefix,info)
    local
      FCore.Cache cache;
      FCore.Graph env;
      Boolean b3,b4;
      DAE.Exp elabedE1_2, elabedE2_2;
      DAE.Properties prop1,prop,prop2;
      Prefix.Prefix pre;
      Absyn.Exp e1,e2;

    case(cache,env,e1,e2,_,_,prop,prop2,_,pre,_) equation
      b3 = Types.isPropTupleArray(prop);
      b4 = Types.isPropTupleArray(prop2);
      true = boolOr(b3,b4);
      true = Expression.containFunctioncall(elabedE2);
      (e1,prop) = expandTupleEquationWithWild(e1,prop2,prop);
      (cache,elabedE1_2,prop1,_) = Static.elabExp(cache,env, e1, impl,NONE(),false,pre,info);
      (cache, elabedE1_2, prop1) = Ceval.cevalIfConstant(cache, env, elabedE1_2, prop1, impl, info);
      (cache,elabedE2_2,prop2,_) = Static.elabExp(cache,env, e2, impl,NONE(),false,pre,info);
      (cache, elabedE2_2, prop2) = Ceval.cevalIfConstant(cache, env, elabedE2_2, prop2, impl, info);
      then
        (cache,elabedE1_2,elabedE2_2,prop);
    case(cache,_,_,_,_,_,prop,_,_,_,_)
    then (cache,elabedE1,elabedE2,prop);
  end matchcontinue;
end condenseArrayEquation;

protected function expandTupleEquationWithWild
"Author BZ 2008-06
The function expands the inExp, Absyn.EXP, to contain as many elements as the, DAE.Properties, propCall does.
The expand adds the elements at the end and they are containing Absyn.WILD() exps with type Types.ANYTYPE. "
  input Absyn.Exp inExp;
  input DAE.Properties propCall;
  input DAE.Properties propTuple;
  output Absyn.Exp outExp;
  output DAE.Properties oprop;
algorithm
  (outExp,oprop) := matchcontinue(inExp,propCall,propTuple)
  local
    list<Absyn.Exp> aexpl,aexpl2;
    list<DAE.Type> typeList;
    Integer fillValue "The amount of elements to add";
    DAE.Type propType;
    list<DAE.Type> lst,lst2;
    DAE.TypeSource ts;
    list<DAE.TupleConst> tupleConst,tupleConst2;
    DAE.Const tconst;
    Option<list<String>> names;

  case (Absyn.TUPLE(aexpl),
        DAE.PROP_TUPLE(type_ = DAE.T_TUPLE(types=typeList,names=names)),
        DAE.PROP_TUPLE(type_ = DAE.T_TUPLE(types=lst,source=ts),
                       tupleConst = DAE.TUPLE_CONST(tupleConst)))
    equation
      fillValue = (listLength(typeList)-listLength(aexpl));
      lst2 = List.fill(DAE.T_ANYTYPE_DEFAULT,fillValue) "types";
      aexpl2 = List.fill(Absyn.CREF(Absyn.WILD()),fillValue) "epxressions";
      tupleConst2 = List.fill(DAE.SINGLE_CONST(DAE.C_VAR()),fillValue) "TupleConst's";
      aexpl2 = listAppend(aexpl,aexpl2);
      lst2 = listAppend(lst,lst2);
      tupleConst2 = listAppend(tupleConst,tupleConst2);
    then
      (Absyn.TUPLE(aexpl2),DAE.PROP_TUPLE(DAE.T_TUPLE(lst2,names,ts),DAE.TUPLE_CONST(tupleConst2)));

  case(_, DAE.PROP_TUPLE(type_ = DAE.T_TUPLE(typeList,names,_)), DAE.PROP(propType,tconst))
    equation
      fillValue = (listLength(typeList)-1);
      aexpl2 = List.fill(Absyn.CREF(Absyn.WILD()),fillValue) "epxressions";
      lst2 = List.fill(DAE.T_ANYTYPE_DEFAULT,fillValue) "types";
      tupleConst2 = List.fill(DAE.SINGLE_CONST(DAE.C_VAR()),fillValue) "TupleConst's";
      aexpl = inExp::aexpl2;
      lst = propType::lst2;
      tupleConst = DAE.SINGLE_CONST(tconst)::tupleConst2;
    then
      (Absyn.TUPLE(aexpl),DAE.PROP_TUPLE(DAE.T_TUPLE(lst,names,DAE.emptyTypeSource),DAE.TUPLE_CONST(tupleConst)));

  case (_, _, _) guard(not Types.isPropTuple(propCall))
    then (inExp,propTuple);

  else
    algorithm
      true := Flags.isSet(Flags.FAILTRACE);
      Debug.traceln("- expandTupleEquationWithWild failed");
    then
      fail();

  end matchcontinue;
end expandTupleEquationWithWild;

protected function instEquationCommonCiTrans
"updats The ClassInf state machine when an equation is instantiated."
  input ClassInf.State inState;
  input SCode.Initial inInitial;
  output ClassInf.State outState;
algorithm
  outState := match inInitial
    case SCode.NON_INITIAL()
      then ClassInf.trans(inState, ClassInf.FOUND_EQUATION());

    else inState;
  end match;
end instEquationCommonCiTrans;

protected function unroll
  "Unrolling a loop is a way of removing the non-linear structure of the FOR
   clause by explicitly repeating the body of the loop once for each iteration."
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input Ident inIdent;
  input DAE.Type inIteratorType;
  input Values.Value inValue;
  input list<SCode.EEquation> inEquations;
  input SCode.Initial inInitial;
  input Boolean inImplicit;
  output FCore.Cache outCache = inCache;
  output DAE.DAElist outDae;
protected
  list<Values.Value> values;
  FCore.Graph env;
  ClassInf.State ci_state = inState;
  list<DAE.DAElist> daes = {};
  DAE.DAElist dae;
algorithm
  try
    Values.ARRAY(valueLst = values) := inValue;

    for val in values loop
      env := FGraph.openScope(inEnv, SCode.NOT_ENCAPSULATED(), FCore.forScopeName, NONE());
      // The iterator is not constant but the range is constant.
      env := FGraph.addForIterator(env, inIdent, inIteratorType,
        DAE.VALBOUND(val, DAE.BINDING_FROM_DEFAULT_VALUE()), SCode.CONST(), SOME(DAE.C_CONST()));

      (outCache, _, _, dae, ci_state) :=
        Inst.instList(outCache, env, inIH, inPrefix, ci_state,
          if SCode.isInitial(inInitial) then instEInitialEquation else instEEquation,
          inEquations, inImplicit, alwaysUnroll);

      daes := dae :: daes;
    end for;

    outDae := List.fold(daes, DAEUtil.joinDaes, DAE.emptyDae);
  else
    true := Flags.isSet(Flags.FAILTRACE);
    Debug.traceln("- InstSection.unroll failed: " + ValuesUtil.valString(inValue));
    fail();
  end try;
end unroll;

protected function addForLoopScope
"Adds a scope to the environment used in for loops.
 adrpo NOTE:
   The variability of the iterator SHOULD
   be determined by the range constantness!"
  input FCore.Graph env;
  input Ident iterName;
  input DAE.Type iterType;
  input SCode.Variability iterVariability;
  input Option<DAE.Const> constOfForIteratorRange;
  output FCore.Graph newEnv;
algorithm
  newEnv := FGraph.openScope(env, SCode.NOT_ENCAPSULATED(), FCore.forScopeName, NONE());
  newEnv := FGraph.addForIterator(newEnv, iterName, iterType, DAE.UNBOUND(), iterVariability, constOfForIteratorRange);
end addForLoopScope;

protected function addParForLoopScope
"Adds a scope to the environment used in for loops.
 adrpo NOTE:
   The variability of the iterator SHOULD
   be determined by the range constantness!"
  input FCore.Graph env;
  input Ident iterName;
  input DAE.Type iterType;
  input SCode.Variability iterVariability;
  input Option<DAE.Const> constOfForIteratorRange;
  output FCore.Graph newEnv;
algorithm
  newEnv := FGraph.openScope(env, SCode.NOT_ENCAPSULATED(), FCore.parForScopeName, NONE());
  newEnv := FGraph.addForIterator(newEnv, iterName, iterType, DAE.UNBOUND(), iterVariability, constOfForIteratorRange);
end addParForLoopScope;

public function instEqEquation "author: LS, ELN
  Equations follow the same typing rules as equality expressions.
  This function adds the equation to the DAE."
  input DAE.Exp inExp1;
  input DAE.Properties inProperties2;
  input DAE.Exp inExp3;
  input DAE.Properties inProperties4;
  input DAE.ElementSource source "the origin of the element";
  input SCode.Initial inInitial5;
  input Boolean inImplicit;
  output DAE.DAElist outDae;
algorithm
  outDae := matchcontinue (inExp1,inProperties2,inExp3,inProperties4,source,inInitial5,inImplicit)
    local
      DAE.Exp e1_1,e1,e2,e2_1;
      DAE.Type t_1,t1,t2,t;
      DAE.DAElist dae;
      DAE.Properties p1,p2;
      SCode.Initial initial_;
      Boolean impl;
      String e1_str,t1_str,e2_str,t2_str,s1,s2;
      DAE.Const c;
      DAE.TupleConst tp;
      SourceInfo info;

      /* TODO: Weird hack to make backend happy */
    case (e1 as DAE.CREF(), (p1 as DAE.PROP(type_ = DAE.T_COMPLEX(complexClassType=ClassInf.RECORD(_)))),
          e2, (p2 as DAE.PROP(constFlag = c)), _, initial_, _) /* If it fails then this rule is matched. */
      equation
        (e2_1, DAE.PROP(t_1, _)) = Types.matchProp(e2, p2, p1, true);
        (e1,_) = ExpressionSimplify.simplify(e1);
        (e2_1,_) = ExpressionSimplify.simplify(e2_1);
        dae = instEqEquation2(e1, e2_1, t_1, c, source, initial_);
      then
        dae;

    case (e1, (p1 as DAE.PROP()),
          e2, (p2 as DAE.PROP(constFlag = c)), _, initial_, _) /* If e2 is not of e1's type, check if e1 has e2's type instead */
      equation
        (e1_1, DAE.PROP(t_1, _)) = Types.matchProp(e1, p1, p2, false);
        (e1_1,_) = ExpressionSimplify.simplify(e1_1);
        (e2,_) = ExpressionSimplify.simplify(e2);
        dae = instEqEquation2(e1_1, e2, t_1, c, source, initial_);
      then
        dae;

      /* TODO: Make testsuite run properly even if this is the first case... Unknown dimensions are not matched fine here and should possibly be disallowed. */
    case (e1, (p1 as DAE.PROP()),
          e2, (p2 as DAE.PROP(constFlag = c)), _, initial_, _) /* If it fails then this rule is matched. */
      equation
        (e2_1, DAE.PROP(t_1, _)) = Types.matchProp(e2, p2, p1, true);
        (e1,_) = ExpressionSimplify.simplify(e1);
        (e2_1,_) = ExpressionSimplify.simplify(e2_1);
        dae = instEqEquation2(e1, e2_1, t_1, c, source, initial_);
      then dae;

    case (e1, (p1 as DAE.PROP_TUPLE()),
          e2, (p2 as DAE.PROP_TUPLE(tupleConst = tp)), _, initial_, _) /* PR. */
      equation
        (e1_1, DAE.PROP_TUPLE(t_1, _)) = Types.matchProp(e1, p1, p2, false);
        (e1_1,_) = ExpressionSimplify.simplify(e1_1);
        (e2,_) = ExpressionSimplify.simplify(e2);
        c = Types.propTupleAllConst(tp);
        dae = instEqEquation2(e1_1, e2, t_1, c, source, initial_);
      then
        dae;

    case (e1, (p1 as DAE.PROP_TUPLE()),
          e2, (p2 as DAE.PROP_TUPLE(tupleConst = tp)), _, initial_, _) /* PR.
      An assignment to a variable of T_ENUMERATION type is an explicit
      assignment to the value componnent of the enumeration, i.e. having
      a type T_ENUM
   */
      equation
        (e2_1, DAE.PROP_TUPLE(t_1, _)) = Types.matchProp(e2, p2, p1, true);
        (e1,_) = ExpressionSimplify.simplify(e1);
        (e2_1,_) = ExpressionSimplify.simplify(e2_1);
        c = Types.propTupleAllConst(tp);
        dae = instEqEquation2(e1, e2_1, t_1, c, source, initial_);
      then
        dae;

    case ((e1 as DAE.CREF()),
           DAE.PROP(type_ = DAE.T_ENUMERATION()),
           e2,
           DAE.PROP(type_ = t as DAE.T_ENUMERATION(), constFlag = c), _, initial_, _)
      equation
        (e1,_) = ExpressionSimplify.simplify(e1);
        (e2,_) = ExpressionSimplify.simplify(e2);
        dae = instEqEquation2(e1, e2, t, c, source, initial_);
      then
        dae;

    // Assignment to a single component with a function returning multiple
    // values.
    case (e1, p1 as DAE.PROP(),
          e2, DAE.PROP_TUPLE(), _, initial_, _)
      equation
        p2 = Types.propTupleFirstProp(inProperties4);
        DAE.PROP(constFlag = c) = p2;
        (e1, DAE.PROP(type_ = t_1)) = Types.matchProp(e1, p1, p2, false);
        (e1,_) = ExpressionSimplify.simplify(e1);
        e2 = DAE.TSUB(e2, 1, t_1);
        (e2,_) = ExpressionSimplify.simplify(e2);
        dae = instEqEquation2(e1, e2, t_1, c, source, initial_);
      then
        dae;

    case (e1,DAE.PROP(type_ = t1),e2,DAE.PROP(type_ = t2),_,_,_)
      equation
        e1_str = ExpressionDump.printExpStr(e1);
        t1_str = Types.unparseTypeNoAttr(t1);
        e2_str = ExpressionDump.printExpStr(e2);
        t2_str = Types.unparseTypeNoAttr(t2);
        s1 = stringAppendList({e1_str,"=",e2_str});
        s2 = stringAppendList({t1_str,"=",t2_str});
        info = ElementSource.getElementSourceFileInfo(source);
        Types.typeErrorSanityCheck(t1_str, t2_str, info);
        Error.addSourceMessage(Error.EQUATION_TYPE_MISMATCH_ERROR, {s1,s2}, info);
      then fail();
  end matchcontinue;
end instEqEquation;

protected function instEqEquation2
"author: LS, ELN
  This is the second stage of instEqEquation, when the types are checked."
  input DAE.Exp inExp1;
  input DAE.Exp inExp2;
  input DAE.Type inType3;
  input DAE.Const inConst;
  input DAE.ElementSource source "the origin of the element";
  input SCode.Initial inInitial4;
  output DAE.DAElist outDae;
algorithm
  outDae := matchcontinue (inExp1,inExp2,inType3, inConst, source,inInitial4)
    local
      DAE.DAElist dae;
      DAE.Exp e,e1,e2;
      SCode.Initial initial_;
      DAE.ComponentRef cr;
      DAE.Type t;
      list<DAE.Var> vs;
      DAE.Type tt;
      list<DAE.Exp> exps1,exps2;
      list<DAE.Type> tys;
      Boolean b;

    case (e1,e2,DAE.T_INTEGER(),_,_,initial_)
      equation
        dae = makeDaeEquation(e1, e2, source, initial_);
      then
        dae;
    case (e1,e2,DAE.T_REAL(),_,_,initial_)
      equation
        dae = makeDaeEquation(e1, e2, source, initial_);
      then
        dae;
    case (e1,e2,DAE.T_STRING(),_,_,initial_)
      equation
        dae = makeDaeEquation(e1, e2, source, initial_);
      then
        dae;
    case (e1,e2,DAE.T_BOOL(),_,_,initial_)
      equation
        dae = makeDaeEquation(e1, e2, source, initial_);
      then
        dae;
    //BTH
    case (e1,e2,DAE.T_CLOCK(),_,_,initial_)
      equation
        dae = makeDaeEquation(e1, e2, source, initial_);
      then
        dae;

    case (DAE.CREF(componentRef = cr),e2,DAE.T_ENUMERATION(),_,_,initial_)
      equation
        dae = makeDaeDefine(cr, e2, source, initial_);
      then
        dae;

    // array equations
    case (e1,e2,tt as DAE.T_ARRAY(),_,_,initial_)
      equation
        dae = instArrayEquation(e1, e2, tt, inConst, source, initial_);
      then dae;

    // tuples
    case (DAE.TUPLE(exps1),e2,DAE.T_TUPLE(types = _::_),_,_,initial_)
      equation
        exps1 = List.map(exps1,Expression.emptyToWild);
        checkNoDuplicateAssignments(exps1, ElementSource.getElementSourceFileInfo(source));
        e1 = DAE.TUPLE(exps1);
        dae = makeDaeEquation(e1, e2, source, initial_);
      then dae;

    case (e1,e2,DAE.T_TUPLE(),_,_,initial_) guard not Expression.isTuple(e1)
      equation
        dae = makeDaeEquation(e1, e2, source, initial_);
      then dae;

    // MetaModelica types
    case (e1,e2,DAE.T_METALIST(),_,_,initial_)
      equation
        true = Config.acceptMetaModelicaGrammar();
        dae = makeDaeEquation(e1, e2, source, initial_);
      then
        dae;
    case (e1,e2,DAE.T_METATUPLE(),_,_,initial_)
      equation
        true = Config.acceptMetaModelicaGrammar();
        dae = makeDaeEquation(e1, e2, source, initial_);
      then
        dae;
    case (e1,e2,DAE.T_METAOPTION(),_,_,initial_)
      equation
        true = Config.acceptMetaModelicaGrammar();
        dae = makeDaeEquation(e1, e2, source, initial_);
      then
        dae;
    case (e1,e2,DAE.T_METAUNIONTYPE(),_,_,initial_)
      equation
        true = Config.acceptMetaModelicaGrammar();
        dae = makeDaeEquation(e1, e2, source, initial_);
      then
        dae;
    // --------------

    // Complex types extending basic type
    case (e1,e2,DAE.T_SUBTYPE_BASIC(complexType = tt),_,_,initial_)
      equation
        dae = instEqEquation2(e1, e2, tt, inConst, source, initial_);
      then
        dae;

    // split a complex equation to its elements
    case (e1,e2,DAE.T_COMPLEX(varLst = vs),_,_,initial_)
      equation
        exps1 = Expression.splitRecord(e1,inType3);
        exps2 = Expression.splitRecord(e2,inType3);
        tys = List.map(vs, Types.getVarType);
        dae = instEqEquation2List(exps1, exps2, tys, inConst, source, initial_, {});
      then dae;

   /* all other COMPLEX equations */
   case (e1,e2, tt as DAE.T_COMPLEX(),_,_,initial_)
     equation
       dae = instComplexEquation(e1,e2,tt,source,initial_);
     then dae;

    else
      equation
        true = Flags.isSet(Flags.FAILTRACE);
        Debug.trace("- InstSection.instEqEquation2 failed\n");
      then
        fail();
  end matchcontinue;
end instEqEquation2;

protected function instEqEquation2List
  input list<DAE.Exp> inExps1;
  input list<DAE.Exp> inExps2;
  input list<DAE.Type> inTypes3;
  input DAE.Const const;
  input DAE.ElementSource source "the origin of the element";
  input SCode.Initial initial_;
  input list<DAE.DAElist> acc;
  output DAE.DAElist outDae;
algorithm
  outDae := match (inExps1,inExps2,inTypes3, const, source, initial_,acc)
    local
      list<DAE.Exp> rest1,rest2;
      list<DAE.Type> rest3;
      DAE.Type ty;
      DAE.Exp exp1,exp2;
      DAE.DAElist res;
    case ({},{},{},_,_,_,_) then DAEUtil.joinDaeLst(listReverse(acc));
    case (exp1::rest1,exp2::rest2,ty::rest3,_,_,_,_)
      equation
        res = instEqEquation2(exp1,exp2,ty,const,source,initial_);
      then instEqEquation2List(rest1,rest2,rest3,const,source,initial_,res::acc);
  end match;
end instEqEquation2List;

public function makeDaeEquation
"author: LS, ELN
  Constructs an equation in the DAE, they can be
  either an initial equation or an ordinary equation."
  input DAE.Exp inExp1;
  input DAE.Exp inExp2;
  input DAE.ElementSource inSource "the origin of the element";
  input SCode.Initial inInitial3;
  output DAE.DAElist outDae;
algorithm
  outDae := match (inExp1,inExp2,inSource,inInitial3)
    local
      DAE.Exp e1,e2;
      DAE.ElementSource source;
      DAE.Element elt;
    case (e1,e2,source,SCode.NON_INITIAL())
      equation
        elt = DAE.EQUATION(e1,e2,source);
        source = ElementSource.addSymbolicTransformationFlattenedEqs(source, elt);
      then DAE.DAE({DAE.EQUATION(e1,e2,source)});
    case (e1,e2,source,SCode.INITIAL())
      equation
        elt = DAE.INITIALEQUATION(e1,e2,source);
        source = ElementSource.addSymbolicTransformationFlattenedEqs(source, elt);
      then DAE.DAE({DAE.INITIALEQUATION(e1,e2,source)});
  end match;
end makeDaeEquation;

protected function makeDaeDefine
"author: LS, ELN "
  input DAE.ComponentRef inComponentRef;
  input DAE.Exp inExp;
  input DAE.ElementSource source "the origin of the element";
  input SCode.Initial inInitial;
  output DAE.DAElist outDae;
algorithm
  outDae := match (inComponentRef,inExp,source,inInitial)
    local DAE.ComponentRef cr; DAE.Exp e2;
    case (cr,e2,_,SCode.NON_INITIAL())
      then DAE.DAE({DAE.DEFINE(cr,e2,source)});
    case (cr,e2,_,SCode.INITIAL())
      then DAE.DAE({DAE.INITIALDEFINE(cr,e2,source)});
  end match;
end makeDaeDefine;

protected function instArrayEquation
  "Instantiates an array equation, i.e. an equation where both sides are arrays."
  input DAE.Exp lhs;
  input DAE.Exp rhs;
  input DAE.Type tp;
  input DAE.Const inConst;
  input DAE.ElementSource inSource;
  input SCode.Initial initial_;
  output DAE.DAElist dae;
algorithm
  dae := matchcontinue(lhs, rhs, tp, inConst, inSource, initial_)
    local
      Boolean b, b1, b2;
      DAE.Dimensions ds;
      DAE.Dimension dim, lhs_dim, rhs_dim;
      list<DAE.Exp> lhs_idxs, rhs_idxs;
      DAE.Type t;
      String lhs_str, rhs_str, eq_str;
      DAE.Element elt;
      DAE.ElementSource source;

    /* Initial array equations with function calls => initial array equations */
    case (_, _, _, _, source, SCode.INITIAL())
      equation
        b1 = Expression.containVectorFunctioncall(lhs);
        b2 = Expression.containVectorFunctioncall(rhs);
        true = boolOr(b1, b2);
        ds = Types.getDimensions(tp);
        elt = DAE.INITIAL_ARRAY_EQUATION(ds, lhs, rhs, source);
        source = ElementSource.addSymbolicTransformationFlattenedEqs(source, elt);
      then
        DAE.DAE({DAE.INITIAL_ARRAY_EQUATION(ds, lhs, rhs, source)});

    /* Arrays with function calls => array equations */
    case (_, _, _, _, source, SCode.NON_INITIAL())
      equation
        b1 = Expression.containVectorFunctioncall(lhs);
        b2 = Expression.containVectorFunctioncall(rhs);
        true = boolOr(b1, b2);
        ds = Types.getDimensions(tp);
        elt = DAE.ARRAY_EQUATION(ds, lhs, rhs, source);
        source = ElementSource.addSymbolicTransformationFlattenedEqs(source, elt);
      then
        DAE.DAE({DAE.ARRAY_EQUATION(ds, lhs, rhs, source)});

    // Array equation of any size, non-expanding case
    case (_, _, DAE.T_ARRAY(ty = t, dims = {_}), _, _, _)
      equation
        false = Config.splitArrays();
        // Expand along the first dimensions of the expressions, and generate an
        // equation for each pair of elements.
        DAE.T_ARRAY(dims = lhs_dim :: _) = Expression.typeof(lhs);
        DAE.T_ARRAY(dims = rhs_dim :: _) = Expression.typeof(rhs);
        lhs_idxs = expandArrayDimension(lhs_dim, lhs);
        rhs_idxs = expandArrayDimension(rhs_dim, rhs);
        dae = instArrayElEq(lhs, rhs, t, inConst, lhs_idxs, rhs_idxs, inSource, initial_);
      then
        dae;

    // Array dimension of known size, expanding case.
    case (_, _, DAE.T_ARRAY(ty = t, dims = {dim}), _, _, _)
      equation
        true = Config.splitArrays();
        true = Expression.dimensionKnown(dim);
        // Expand along the first dimensions of the expressions, and generate an
        // equation for each pair of elements.
        DAE.T_ARRAY(dims = lhs_dim :: _) = Expression.typeof(lhs);
        DAE.T_ARRAY(dims = rhs_dim :: _) = Expression.typeof(rhs);
        lhs_idxs = expandArrayDimension(lhs_dim, lhs);
        rhs_idxs = expandArrayDimension(rhs_dim, rhs);
        dae = instArrayElEq(lhs, rhs, t, inConst, lhs_idxs, rhs_idxs, inSource, initial_);
      then
        dae;

    case (_, _, DAE.T_ARRAY(dims = {dim}), _, source, _)
      equation
        true = Config.splitArrays();
        true = Expression.dimensionKnown(dim);
        true = Expression.isRange(lhs) or Expression.isRange(rhs) or Expression.isReduction(lhs) or Expression.isReduction(rhs);
        ds = Types.getDimensions(tp);
        b = SCode.isInitial(initial_);
        elt = if b then DAE.INITIAL_ARRAY_EQUATION(ds, lhs, rhs, source) else DAE.ARRAY_EQUATION(ds, lhs, rhs, source);
        source = ElementSource.addSymbolicTransformationFlattenedEqs(source, elt);
        elt = if b then DAE.INITIAL_ARRAY_EQUATION(ds, lhs, rhs, source) else DAE.ARRAY_EQUATION(ds, lhs, rhs, source);
      then
        DAE.DAE({elt});

    // Array dimension of unknown size, expanding case.
    case (_, _, DAE.T_ARRAY(ty = t, dims = {dim}), _, _, _)
      equation
        true = Config.splitArrays();
        false = Expression.dimensionKnown(dim);
        // It's ok with array equation of unknown size if checkModel is used.
        true = Flags.getConfigBool(Flags.CHECK_MODEL);
        // Expand along the first dimensions of the expressions, and generate an
        // equation for each pair of elements.
        DAE.T_ARRAY(dims = lhs_dim :: _) = Expression.typeof(lhs);
        DAE.T_ARRAY(dims = rhs_dim :: _) = Expression.typeof(rhs);
        lhs_idxs = expandArrayDimension(lhs_dim, lhs);
        rhs_idxs = expandArrayDimension(rhs_dim, rhs);
        dae = instArrayElEq(lhs, rhs, t, inConst, lhs_idxs, rhs_idxs, inSource, initial_);
      then
        dae;

    // Array equation of unknown size, e.g. Real x[:], y[:]; equation x = y; (expanding case)
    case (_, _, DAE.T_ARRAY(dims = {DAE.DIM_UNKNOWN()}), _, source, SCode.INITIAL())
      equation
        true = Config.splitArrays();
        // It's ok with array equation of unknown size if checkModel is used.
        true = Flags.getConfigBool(Flags.CHECK_MODEL);
        // generate an initial array equation of dim 1
        // Now the dimension can be made DAE.DIM_UNKNOWN(), I just don't want to break anything for now -- alleb
        elt = DAE.INITIAL_ARRAY_EQUATION({DAE.DIM_INTEGER(1)}, lhs, rhs, source);
        source = ElementSource.addSymbolicTransformationFlattenedEqs(source, elt);
      then
        DAE.DAE({DAE.INITIAL_ARRAY_EQUATION({DAE.DIM_INTEGER(1)}, lhs, rhs, source)});

    // Array equation of unknown size, e.g. Real x[:], y[:]; equation x = y; (expanding case)
    case (_, _, DAE.T_ARRAY(dims = {DAE.DIM_UNKNOWN()}), _, source, SCode.NON_INITIAL())
      equation
         true = Config.splitArrays();
        // It's ok with array equation of unknown size if checkModel is used.
        true = Flags.getConfigBool(Flags.CHECK_MODEL);
        // generate an array equation of dim 1
        // Now the dimension can be made DAE.DIM_UNKNOWN(), I just don't want to break anything for now -- alleb
        elt = DAE.ARRAY_EQUATION({DAE.DIM_INTEGER(1)}, lhs, rhs, source);
        source = ElementSource.addSymbolicTransformationFlattenedEqs(source, elt);
      then
        DAE.DAE({DAE.ARRAY_EQUATION({DAE.DIM_INTEGER(1)}, lhs, rhs, source)});

    // Array equation of unknown size, e.g. Real x[:], y[:]; equation x = y; (expanding case)
    case (_, _, DAE.T_ARRAY(dims = {DAE.DIM_UNKNOWN()}), _, _, _)
      equation
        true = Config.splitArrays();
        // It's ok with array equation of unknown size if checkModel is used.
        false = Flags.getConfigBool(Flags.CHECK_MODEL);
        lhs_str = ExpressionDump.printExpStr(lhs);
        rhs_str = ExpressionDump.printExpStr(rhs);
        eq_str = stringAppendList({lhs_str, "=", rhs_str});
        Error.addSourceMessage(Error.INST_ARRAY_EQ_UNKNOWN_SIZE, {eq_str}, ElementSource.getElementSourceFileInfo(inSource));
      then
        fail();

    else
      equation
        true = Flags.isSet(Flags.FAILTRACE);
        Debug.trace("- InstSection.instArrayEquation failed\n");
      then
        fail();
  end matchcontinue;
end instArrayEquation;

protected function instArrayElEq
  "This function loops recursively through all indices in the two arrays and
  generates an equation for each pair of elements."
  input DAE.Exp inLhsExp;
  input DAE.Exp inRhsExp;
  input DAE.Type inType;
  input DAE.Const inConst;
  input list<DAE.Exp> inLhsIndices;
  input list<DAE.Exp> inRhsIndices;
  input DAE.ElementSource inSource;
  input SCode.Initial inInitial;
  output DAE.DAElist outDAE = DAE.emptyDae;
protected
  DAE.Exp rhs_idx;
  list<DAE.Exp> rhs_idxs = listReverse(inRhsIndices);
  DAE.DAElist dae;
algorithm
  for lhs_idx in listReverse(inLhsIndices) loop
    rhs_idx :: rhs_idxs := rhs_idxs;

    dae := instEqEquation2(lhs_idx, rhs_idx, inType, inConst, inSource, inInitial);
    outDAE := DAEUtil.joinDaes(dae, outDAE);
  end for;
end instArrayElEq;

protected function unrollForLoop
  "Unrolls a for-loop that contains when-statements."
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input String inIterator;
  input DAE.Exp inRange;
  input DAE.Properties inRangeProps;
  input list<SCode.Statement> inBody;
  input SCode.Statement inStatement;
  input SourceInfo inInfo;
  input DAE.ElementSource inSource;
  input SCode.Initial inInitial;
  input Boolean inImpl;
  input Boolean inUnrollLoops;
  output FCore.Cache outCache;
  output list<DAE.Statement> outStatements;
protected
  DAE.Type ty;
  DAE.Const c;
  DAE.Exp range;
  FCore.Graph env;
  Values.Value val;
  String str;
algorithm
  try
    DAE.T_ARRAY(ty = ty) := Types.getPropType(inRangeProps);
    c := Types.getPropConst(inRangeProps);

    // We can unroll ONLY if we have a parameter range expression.
    true := Types.isParameterOrConstant(c);
    env := addForLoopScope(inEnv, inIterator, ty, SCode.VAR(), SOME(c));
    (outCache, val) :=
      Ceval.ceval(inCache, env, inRange, inImpl, NONE(), Absyn.MSG(inInfo), 0);
    (outCache, outStatements) := loopOverRange(inCache, env, inIH, inPrefix,
      inState, inIterator, val, inBody, inSource, inInitial, inImpl, inUnrollLoops);
  else
    Error.addSourceMessageAndFail(Error.UNROLL_LOOP_CONTAINING_WHEN,
      {SCodeDump.statementStr(inStatement)}, inInfo);
  end try;
end unrollForLoop;

protected function instForStatement
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input SCode.Statement inForStatement;
  input DAE.ElementSource inSource;
  input SCode.Initial inInitial;
  input Boolean inImpl;
  input Boolean inUnrollLoops;
  output FCore.Cache outCache;
  output list<DAE.Statement> outStatements "For statements can produce multiple statements due to unrolling.";
protected
  String iterator;
  Option<Absyn.Exp> oarange;
  Absyn.Exp arange;
  DAE.Exp range;
  DAE.Properties prop;
  list<SCode.Statement> body;
  SourceInfo info;
  list<Absyn.IteratorIndexedCref> iter_crefs;
algorithm
  SCode.ALG_FOR(index = iterator, range = oarange, forBody = body, info = info) := inForStatement;

  if isSome(oarange) then
    SOME(arange) := oarange;
    (outCache, range, prop) :=
      Static.elabExp(inCache, inEnv, arange, inImpl, NONE(), true, inPrefix, info);
  else
    iter_crefs := SCode.findIteratorIndexedCrefsInStatements(body, iterator);
    (range, prop, outCache) :=
      Static.deduceIterationRange(iterator, iter_crefs, inEnv, inCache, info);
  end if;

  // Only unroll for-loops containing when-statements.
  if containsWhenStatements(body) then
    (outCache, outStatements) := unrollForLoop(inCache, inEnv, inIH, inPrefix,
      inState, iterator, range, prop, body, inForStatement, info, inSource,
      inInitial, inImpl, inUnrollLoops);
  else
    (outCache, outStatements) := instForStatement_dispatch(inCache, inEnv, inIH,
      inPrefix, inState, iterator, range, prop, body, info, inSource, inInitial, inImpl, inUnrollLoops);
  end if;
end instForStatement;

protected function instForStatement_dispatch
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input String inIterator;
  input DAE.Exp inRange;
  input DAE.Properties inRangeProps;
  input list<SCode.Statement> inBody;
  input SourceInfo inInfo;
  input DAE.ElementSource inSource;
  input SCode.Initial inInitial;
  input Boolean inImpl;
  input Boolean inUnrollLoops;
  output FCore.Cache outCache = inCache;
  output list<DAE.Statement> outStatements;
protected
  DAE.Type ty;
  DAE.Const c;
  FCore.Graph env;
  DAE.ElementSource source;
  DAE.Exp range;
algorithm
  c := Types.getPropConst(inRangeProps);

  // Remove the for-loop if the range is empty.
  if Types.isParameterOrConstant(c) then
    try
      (outCache, Values.ARRAY(valueLst = {}), _) :=
        Ceval.ceval(outCache, inEnv, inRange, inImpl, NONE(), Absyn.MSG(inInfo), 0);
      outStatements := {};
      return;
    else
    end try;
  end if;

  ty := Types.getPropType(inRangeProps);
  ty := getIteratorType(ty, inIterator, inInfo);

  (outCache, range) :=
    Ceval.cevalRangeIfConstant(outCache, inEnv, inRange, inRangeProps, inImpl, inInfo);
  (outCache, range) := PrefixUtil.prefixExp(outCache, inEnv, inIH, range, inPrefix);
  env := addForLoopScope(inEnv, inIterator, ty, SCode.VAR(), SOME(c));
  (outCache, outStatements) := instStatements(outCache, env, inIH, inPrefix,
    inState, inBody, inSource, inInitial, inImpl, inUnrollLoops);

  source := ElementSource.addElementSourceFileInfo(inSource, inInfo);
  outStatements :=
    {Algorithm.makeFor(inIterator, range, inRangeProps, outStatements, source)};
end instForStatement_dispatch;

protected function instComplexEquation "instantiate a comlex equation, i.e. c = Complex(1.0,-1.0) when Complex is a record"
  input DAE.Exp lhs;
  input DAE.Exp rhs;
  input DAE.Type tp;
  input DAE.ElementSource source "the origin of the element";
  input SCode.Initial initial_;
  output DAE.DAElist dae;
algorithm
  dae := matchcontinue(lhs,rhs,tp,source,initial_)
    local
      String s;
      SourceInfo info;

    // Records
    case(_,_,_,_,_)
      equation
        true = Types.isRecord(tp);
        dae = makeComplexDaeEquation(lhs,rhs,source,initial_);
      then dae;

    // External objects are treated as ordinary equations
    case (_,_,_,_,_)
      equation
        true = Types.isExternalObject(tp);
        dae = makeDaeEquation(lhs,rhs,source,initial_);
        // adrpo: TODO! FIXME! shouldn't we return the dae here??!!
      // PA: do not know, but at least return the functions.
      then DAE.emptyDae;

    // adrpo 2009-05-15: also T_COMPLEX that is NOT record but TYPE should be allowed
    //                   as is used in Modelica.Mechanics.MultiBody (Orientation type)
    case(_,_,_,_,_) equation
      // adrpo: TODO! check if T_COMPLEX(ClassInf.TYPE)!
      dae = makeComplexDaeEquation(lhs,rhs,source,initial_);
    then dae;

    // complex equation that is not of restriction record is not allowed
    else
      equation
        false = Types.isRecord(tp);
        s = ExpressionDump.printExpStr(lhs) + " = " + ExpressionDump.printExpStr(rhs);
        info = ElementSource.getElementSourceFileInfo(source);
        Error.addSourceMessage(Error.ILLEGAL_EQUATION_TYPE, {s}, info);
      then fail();
  end matchcontinue;
end instComplexEquation;

protected function makeComplexDaeEquation "Creates a DAE.COMPLEX_EQUATION for equations involving records"
  input DAE.Exp lhs;
  input DAE.Exp rhs;
  input DAE.ElementSource source "the origin of the element";
  input SCode.Initial initial_;
  output DAE.DAElist dae;
algorithm
  dae := match(lhs,rhs,source,initial_)
    local
    case(_,_,_,SCode.NON_INITIAL())
      then DAE.DAE({DAE.COMPLEX_EQUATION(lhs,rhs,source)});

    case(_,_,_,SCode.INITIAL())
      then DAE.DAE({DAE.INITIAL_COMPLEX_EQUATION(lhs,rhs,source)});
  end match;
end makeComplexDaeEquation;

public function instAlgorithm
"Algorithms are converted to the representation defined in
  the module Algorithm, and the added to the DAE result.
  This function converts an algorithm section."
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input SCode.AlgorithmSection inAlgorithm;
  input Boolean inImpl;
  input Boolean unrollForLoops "we should unroll for loops if they are part of an algorithm in a model";
  output FCore.Cache outCache;
  output FCore.Graph outEnv;
  output InnerOuter.InstHierarchy outIH;
  output DAE.DAElist outDae;
  output ClassInf.State outState;
algorithm
  (outCache,outEnv,outIH,outDae,outState) :=
  matchcontinue (inCache,inEnv,inIH,inPrefix,inState,inAlgorithm,inImpl,unrollForLoops)
    local
      FCore.Graph env;
      list<DAE.Statement> statements_1;
      ClassInf.State ci_state;
      list<SCode.Statement> statements;
      SCode.Statement stmt;
      Boolean impl;
      FCore.Cache cache;
      Prefix.Prefix pre;
      SCode.AlgorithmSection algSCode;
      InstanceHierarchy ih;
      DAE.ElementSource source "the origin of the element";
      DAE.DAElist dae;
      String s;
      SourceInfo info;

    case (cache,env,ih,pre,ci_state,SCode.ALGORITHM(statements = statements),impl,_) /* impl */
      equation
        // set the source of this element
        ci_state = ClassInf.trans(ci_state,ClassInf.FOUND_ALGORITHM());
        source = ElementSource.createElementSource(Absyn.dummyInfo, FGraph.getScopePath(env), pre);

        (cache,statements_1) = instStatements(cache, env, ih, pre, ci_state, statements, source, SCode.NON_INITIAL(), impl, unrollForLoops);
        (statements_1,_) = DAEUtil.traverseDAEEquationsStmts(statements_1,Expression.traverseSubexpressionsHelper,(ExpressionSimplify.simplifyWork,ExpressionSimplifyTypes.optionSimplifyOnly));

        dae = DAE.DAE({DAE.ALGORITHM(DAE.ALGORITHM_STMTS(statements_1),source)});
      then
        (cache,env,ih,dae,ci_state);

    case (_,_,_,_,ci_state,SCode.ALGORITHM(statements = stmt::_),_,_)
      equation
        failure(_ = ClassInf.trans(ci_state,ClassInf.FOUND_ALGORITHM()));
        s = ClassInf.printStateStr(ci_state);
        info = SCode.getStatementInfo(stmt);
        Error.addSourceMessage(Error.ALGORITHM_TRANSITION_FAILURE, {s}, info);
      then fail();

    else
      equation
        true = Flags.isSet(Flags.FAILTRACE);
        Debug.traceln("- InstSection.instAlgorithm failed");
      then
        fail();
  end matchcontinue;
end instAlgorithm;

public function instInitialAlgorithm
"Algorithms are converted to the representation defined
  in the module Algorithm, and the added to the DAE result.
  This function converts an algorithm section."
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input SCode.AlgorithmSection inAlgorithm;
  input Boolean inImpl;
  input Boolean unrollForLoops "we should unroll for loops if they are part of an algorithm in a model";
  output FCore.Cache outCache;
  output FCore.Graph outEnv;
  output InnerOuter.InstHierarchy outIH;
  output DAE.DAElist outDae;
  output ClassInf.State outState;
algorithm
  (outCache,outEnv,outIH,outDae,outState):=
  matchcontinue (inCache,inEnv,inIH,inPrefix,inState,inAlgorithm,inImpl,unrollForLoops)
    local
      FCore.Graph env;
      list<DAE.Statement> statements_1;
      ClassInf.State ci_state;
      list<SCode.Statement> statements;
      Boolean impl;
      FCore.Cache cache;
      Prefix.Prefix pre;
      InstanceHierarchy ih;
      DAE.ElementSource source "the origin of the element";
      DAE.DAElist dae;

    case (cache,env,ih,pre,ci_state,SCode.ALGORITHM(statements = statements),impl,_)
      equation
        // set the source of this element
        source = ElementSource.createElementSource(Absyn.dummyInfo, FGraph.getScopePath(env), pre);

        (cache,statements_1) = instStatements(cache, env, ih, pre, ci_state, statements, source, SCode.INITIAL(), impl, unrollForLoops);
        (statements_1,_) = DAEUtil.traverseDAEEquationsStmts(statements_1,Expression.traverseSubexpressionsHelper,(ExpressionSimplify.simplifyWork,ExpressionSimplifyTypes.optionSimplifyOnly));

        dae = DAE.DAE({DAE.INITIALALGORITHM(DAE.ALGORITHM_STMTS(statements_1),source)});
      then
        (cache,env,ih,dae,ci_state);

    else
      equation
        true = Flags.isSet(Flags.FAILTRACE);
        Debug.trace("- InstSection.instInitialAlgorithm failed\n");
      then
        fail();
  end matchcontinue;
end instInitialAlgorithm;

public function instConstraint
"Constraints are elaborated and converted to DAE"
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input SCode.ConstraintSection inConstraints;
  input Boolean inImpl;
  output FCore.Cache outCache;
  output FCore.Graph outEnv;
  output DAE.DAElist outDae;
  output ClassInf.State outState;
algorithm
  (outCache,outEnv,outDae,outState) :=
  matchcontinue (inCache,inEnv,inPrefix,inState,inConstraints,inImpl)
    local
      FCore.Graph env;
      list<DAE.Exp> constraints_1;
      ClassInf.State ci_state;
      list<Absyn.Exp> constraints;
      Boolean impl;
      FCore.Cache cache;
      Prefix.Prefix pre;
      DAE.ElementSource source "the origin of the element";
      DAE.DAElist dae;

    case (cache,env,pre,ci_state,SCode.CONSTRAINTS(constraints = constraints),impl)
      equation
        // set the source of this element
        ci_state = ClassInf.trans(ci_state,ClassInf.FOUND_ALGORITHM());
        source = ElementSource.createElementSource(Absyn.dummyInfo, FGraph.getScopePath(env), pre);

        (cache,constraints_1,_,_) = Static.elabExpList(cache, env, constraints, impl, NONE(), true /*vect*/, pre, Absyn.dummyInfo);
        // (constraints_1,_) = DAEUtil.traverseDAEEquationsStmts(constraints_1,Expression.traverseSubexpressionsHelper,(ExpressionSimplify.simplifyWork,false));

        dae = DAE.DAE({DAE.CONSTRAINT(DAE.CONSTRAINT_EXPS(constraints_1),source)});
      then
        (cache,env,dae,ci_state);
/*
    case (_,_,_,_,_,_,ci_state,SCode.ALGORITHM(constraints = exp::_),_,_,_)
      equation
        failure(_ = ClassInf.trans(ci_state,ClassInf.FOUND_ALGORITHM()));
        s = ClassInf.printStateStr(ci_state);
        Error.addMessage(Error.ALGORITHM_TRANSITION_FAILURE,{s});
      then fail();
*/
    else
      equation
        true = Flags.isSet(Flags.FAILTRACE);
        Debug.trace("- InstSection.instConstraints failed\n");
      then
        fail();
  end matchcontinue;
end instConstraint;

public function instStatements
  "This function instantiates a list of algorithm statements."
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input list<SCode.Statement> inStatements;
  input DAE.ElementSource inSource;
  input SCode.Initial inInitial;
  input Boolean inImpl;
  input Boolean unrollForLoops "we should unroll for loops if they are part of an algorithm in a model";
  output FCore.Cache outCache = inCache;
  output list<DAE.Statement> outStatements;
protected
  list<DAE.Statement> stmts;
  list<list<DAE.Statement>> stmtsl = {};
algorithm
  for stmt in inStatements loop
    (outCache, stmts) := instStatement(inCache, inEnv, inIH, inPrefix, inState,
      stmt, inSource, inInitial, inImpl, unrollForLoops);
    stmtsl := stmts :: stmtsl;
  end for;

  outStatements := List.flattenReverse(stmtsl);
end instStatements;

protected function instExp
  "Helper function to instStatement. Elaborates, evalutes if constant, and
   prefixes an expression."
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input Absyn.Exp inExp;
  input Boolean inImpl;
  input SourceInfo inInfo;
  output FCore.Cache outCache;
  output DAE.Exp outExp;
  output DAE.Properties outProperties;
algorithm
  (outCache, outExp, outProperties) := Static.elabExp(inCache, inEnv, inExp,
    inImpl, NONE(), true, inPrefix, inInfo);
  (outCache, outExp, outProperties) := Ceval.cevalIfConstant(outCache, inEnv,
    outExp, outProperties, inImpl, inInfo);
  (outCache, outExp) := PrefixUtil.prefixExp(outCache, inEnv, inIH, outExp, inPrefix);
end instExp;

protected function instStatement
  "Instantiates an algorithm statement."
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input SCode.Statement inStatement;
  input DAE.ElementSource inSource;
  input SCode.Initial inInitial;
  input Boolean inImpl;
  input Boolean inUnrollLoops;
  output FCore.Cache outCache = inCache;
  output list<DAE.Statement> outStatements "More statements due to loop unrolling.";
protected
  Integer num_errors = Error.getNumErrorMessages();
algorithm
  try
  outStatements := match inStatement
    local
      DAE.Exp cond_exp, msg_exp, level_exp, exp, cr_exp;
      DAE.Properties cond_prop, msg_prop, level_prop, prop, cr_prop;
      list<DAE.Statement> if_branch, else_branch, branch;
      list<tuple<DAE.Exp, DAE.Properties, list<DAE.Statement>>> else_if_branches;
      Absyn.Exp aexp;
      list<SCode.Statement> sstmts;
      DAE.ElementSource source;
      SourceInfo info;
      Option<DAE.Statement> when_stmt_opt;
      DAE.Statement when_stmt;
      list<DAE.MatchCase> cases;

    case SCode.ALG_ASSIGN()
      algorithm
        (outCache, outStatements) := instAssignment(outCache, inEnv, inIH, inPrefix,
          inStatement, inSource, inInitial, inImpl, inUnrollLoops, num_errors);
      then
        outStatements;

    case SCode.ALG_IF(info = info)
      algorithm
        // Instantiate the first branch.
        (outCache, cond_exp, cond_prop) := instExp(outCache, inEnv, inIH,
          inPrefix, inStatement.boolExpr, inImpl, info);
        (outCache, if_branch) := instStatements(outCache, inEnv, inIH, inPrefix,
          inState, inStatement.trueBranch, inSource, inInitial, inImpl, inUnrollLoops);

        // Instantiate the elseif branches.
        else_if_branches := {};
        for else_if in inStatement.elseIfBranch loop
          (aexp, sstmts) := else_if;
          (outCache, exp, prop) := instExp(outCache, inEnv, inIH, inPrefix,
            aexp, inImpl, info);
          (outCache, branch) := instStatements(outCache, inEnv, inIH, inPrefix,
             inState, sstmts, inSource, inInitial, inImpl, inUnrollLoops);
          else_if_branches := (exp, prop, branch) :: else_if_branches;
        end for;
        else_if_branches := listReverse(else_if_branches);

        // Instantiate the else branch.
        (outCache, else_branch) := instStatements(outCache, inEnv, inIH, inPrefix,
          inState, inStatement.elseBranch, inSource, inInitial, inImpl, inUnrollLoops);

        // Construct the if-statement.
        source := ElementSource.addElementSourceFileInfo(inSource, info);
      then
        Algorithm.makeIf(cond_exp, cond_prop, if_branch, else_if_branches, else_branch, source);

    case SCode.ALG_FOR(info = info)
      algorithm
        (outCache, outStatements) := instForStatement(outCache, inEnv, inIH,
          inPrefix, inState, inStatement, inSource, inInitial, inImpl, inUnrollLoops);
      then
        outStatements;

    case SCode.ALG_PARFOR(info = info)
      algorithm
        (outCache, outStatements) := instParForStatement(outCache, inEnv, inIH,
          inPrefix, inState, inStatement, inSource, inInitial, inImpl, inUnrollLoops);
      then
        outStatements;

    case SCode.ALG_WHILE(info = info)
      algorithm
        (outCache, cond_exp, cond_prop) := instExp(outCache, inEnv, inIH,
          inPrefix, inStatement.boolExpr, inImpl, info);
        (outCache, branch) := instStatements(outCache, inEnv, inIH, inPrefix,
          inState, inStatement.whileBody, inSource, inInitial, inImpl, inUnrollLoops);

        source := ElementSource.addElementSourceFileInfo(inSource, info);
      then
        {Algorithm.makeWhile(cond_exp, cond_prop, branch, source)};

    case SCode.ALG_WHEN_A(info = info)
      algorithm
        // When may not be used in a function.
        if ClassInf.isFunction(inState) then
          Error.addSourceMessageAndFail(Error.FUNCTION_ELEMENT_WRONG_KIND, {"when"}, info);
        end if;

        checkWhenAlgorithm(inStatement);
        source := ElementSource.addElementSourceFileInfo(inSource, info);
        when_stmt_opt := NONE();

        for b in listReverse(inStatement.branches) loop
          (aexp, sstmts) := b;

          (outCache, cond_exp, cond_prop) := instExp(outCache, inEnv, inIH,
            inPrefix, aexp, inImpl, info);
          (outCache, branch) := instStatements(outCache, inEnv, inIH, inPrefix,
            inState, sstmts, inSource, inInitial, inImpl, inUnrollLoops);

          when_stmt := Algorithm.makeWhenA(cond_exp, cond_prop, branch, when_stmt_opt, source);
          when_stmt_opt := SOME(when_stmt);
        end for;
      then
        {when_stmt};

    case SCode.ALG_ASSERT(info = info)
      algorithm
        (outCache, cond_exp, cond_prop) := instExp(outCache, inEnv, inIH,
          inPrefix, inStatement.condition, inImpl, info);
        (outCache, msg_exp, msg_prop) := instExp(outCache, inEnv, inIH,
          inPrefix, inStatement.message, inImpl, info);
        (outCache, level_exp, level_prop) := instExp(outCache, inEnv, inIH,
          inPrefix, inStatement.level, inImpl, info);

        source := ElementSource.addElementSourceFileInfo(inSource, info);
      then
        Algorithm.makeAssert(cond_exp, msg_exp, level_exp, cond_prop, msg_prop, level_prop, source);

    case SCode.ALG_TERMINATE(info = info)
      algorithm
        (outCache, msg_exp, msg_prop) := instExp(outCache, inEnv, inIH,
          inPrefix, inStatement.message, inImpl, info);
        source := ElementSource.addElementSourceFileInfo(inSource, info);
      then
        Algorithm.makeTerminate(msg_exp, msg_prop, source);

    case SCode.ALG_REINIT(info = info)
      algorithm
        (outCache, cr_exp, cr_prop) := instExp(outCache, inEnv, inIH, inPrefix,
          Absyn.CREF(inStatement.cref), inImpl, info);
        (outCache, exp, prop) := instExp(outCache, inEnv, inIH, inPrefix,
          inStatement.newValue, inImpl, info);
        source := ElementSource.addElementSourceFileInfo(inSource, info);
      then
        Algorithm.makeReinit(cr_exp, exp, cr_prop, prop, source);

    case SCode.ALG_NORETCALL(info = info)
      algorithm
        (outCache, exp) := Static.elabExp(outCache, inEnv, inStatement.exp,
          inImpl, NONE(), true, inPrefix, info);
        checkValidNoRetcall(exp, info);
        (outCache, exp) := PrefixUtil.prefixExp(outCache, inEnv, inIH, exp, inPrefix);
        source := ElementSource.addElementSourceFileInfo(inSource, info);
      then
        if Expression.isTuple(exp) then {} else {DAE.STMT_NORETCALL(exp, source)};

    case SCode.ALG_BREAK(info = info)
      algorithm
        source := ElementSource.addElementSourceFileInfo(inSource, info);
      then
        {DAE.STMT_BREAK(source)};

    case SCode.ALG_CONTINUE(info = info)
      algorithm
        source := ElementSource.addElementSourceFileInfo(inSource, info);
      then
        {DAE.STMT_CONTINUE(source)};

    case SCode.ALG_RETURN(info = info)
      algorithm
        if not ClassInf.isFunction(inState) then
          Error.addSourceMessageAndFail(Error.RETURN_OUTSIDE_FUNCTION, {}, info);
        end if;
        source := ElementSource.addElementSourceFileInfo(inSource, info);
      then
        {DAE.STMT_RETURN(source)};

    case SCode.ALG_FAILURE(info = info)
      algorithm
        true := Config.acceptMetaModelicaGrammar();
        (outCache, branch) := instStatements(outCache, inEnv, inIH, inPrefix,
          inState, inStatement.stmts, inSource, inInitial, inImpl, inUnrollLoops);
        source := ElementSource.addElementSourceFileInfo(inSource, info);
      then
        {DAE.STMT_FAILURE(branch, source)};

    // try-else becomes:
    //  matchcontinue ()
    //    case () equation *body* then ();
    //    else equation *elseBody* then ();
    //  end matchcontinue;
    case SCode.ALG_TRY(info = info)
      algorithm
        true := Config.acceptMetaModelicaGrammar();
        (outCache, if_branch) := instStatements(outCache, inEnv, inIH, inPrefix,
          inState, inStatement.body, inSource, inInitial, inImpl, inUnrollLoops);
        (outCache, else_branch) := instStatements(outCache, inEnv, inIH, inPrefix,
          inState, inStatement.elseBody, inSource, inInitial, inImpl, inUnrollLoops);
        source := ElementSource.addElementSourceFileInfo(inSource, info);

        cases := {
          DAE.CASE({}, NONE(), {}, if_branch, SOME(DAE.TUPLE({})), info, 0, info),
          DAE.CASE({}, NONE(), {}, else_branch, SOME(DAE.TUPLE({})), info, 0, info)
        };

        exp := DAE.MATCHEXPRESSION(if SCode.commentHasBooleanNamedAnnotation(inStatement.comment, "__OpenModelica_stackOverflowCheckpoint") then DAE.TRY_STACKOVERFLOW() else DAE.MATCHCONTINUE(), {}, {}, {}, cases,
          DAE.T_NORETCALL_DEFAULT);
      then
        {DAE.STMT_NORETCALL(exp, source)};

  end match;
  else
    true := num_errors == Error.getNumErrorMessages();
    Error.addSourceMessageAndFail(Error.STATEMENT_GENERIC_FAILURE,
      {SCodeDump.statementStr(inStatement)}, SCode.getStatementInfo(inStatement));
  end try;
end instStatement;

protected function makeAssignment
  "Wrapper for Algorithm that calls either makeAssignment or makeTupleAssignment
  depending on whether the right side is a tuple or not. This makes it possible
  to do cref := function_that_returns_tuple(...)."
  input DAE.Exp inLhs;
  input DAE.Properties inLhsProps;
  input DAE.Exp inRhs;
  input DAE.Properties inRhsProps;
  input DAE.Attributes inAttributes;
  input SCode.Initial inInitial;
  input DAE.ElementSource inSource;
  output DAE.Statement outStatement;
algorithm
  outStatement := match (inLhs, inLhsProps, inRhs, inRhsProps, inAttributes, inInitial, inSource)
    local
      list<DAE.Properties> wild_props;
      Integer wild_count;
      list<DAE.Exp> wilds;
      DAE.Exp wildCrefExp;

    // If the RHS is a function that returns a tuple while the LHS is a single
    // value, make a tuple of the LHS and fill in the missing elements with
    // wildcards.
    case (_, DAE.PROP(), DAE.CALL(), DAE.PROP_TUPLE(), _, _, _)
      equation
        _ :: wild_props = Types.propTuplePropList(inRhsProps);
        wild_count = listLength(wild_props);
        wildCrefExp = Expression.makeCrefExp(DAE.WILD(), DAE.T_UNKNOWN_DEFAULT);
        wilds = List.fill(wildCrefExp, wild_count);
        wild_props = List.fill(DAE.PROP(DAE.T_ANYTYPE_DEFAULT, DAE.C_VAR()), wild_count);
      then
        Algorithm.makeTupleAssignment(inLhs :: wilds, inLhsProps :: wild_props, inRhs, inRhsProps, inInitial, inSource);

    // Otherwise, call Algorithm.makeAssignment as usual.
    else Algorithm.makeAssignment(inLhs, inLhsProps, inRhs, inRhsProps, inAttributes, inInitial, inSource);
  end match;
end makeAssignment;

protected function containsWhenStatements
"@author: adrpo
  this functions returns true if the given
  statement list contains when statements"
  input list<SCode.Statement> statementList;
  output Boolean hasWhenStatements;
algorithm
  hasWhenStatements := matchcontinue(statementList)
    local
      list<SCode.Statement> rest, tb, eb, lst;
      list<tuple<Absyn.Exp, list<SCode.Statement>>> eib;
      Boolean b, b1, b2, b3, b4; list<Boolean> blst;
      list<list<SCode.Statement>> slst;

    // handle nothingness
    case ({}) then false;

    // yeha! we have a when!
    case (SCode.ALG_WHEN_A()::_)
      then true;

    // search deeper inside if
    case (SCode.ALG_IF(trueBranch=tb, elseIfBranch=eib, elseBranch=eb)::rest)
      equation
         b1 = containsWhenStatements(tb);
         b2 = containsWhenStatements(eb);
         slst = List.map(eib, Util.tuple22);
         blst = List.map(slst, containsWhenStatements);
         // adrpo: add false to handle the case where list might be empty
         b3 = List.reduce(false::blst, boolOr);
         b4 = containsWhenStatements(rest);
         b = List.reduce({b1, b2, b3, b4}, boolOr);
      then b;

    // search deeper inside for
    case (SCode.ALG_FOR(forBody = lst)::rest)
      equation
         b1 = containsWhenStatements(lst);
         b2 = containsWhenStatements(rest);
         b = boolOr(b1, b2);
      then b;

    // search deeper inside parfor
    case (SCode.ALG_PARFOR(parforBody = lst)::rest)
      equation
         b1 = containsWhenStatements(lst);
         b2 = containsWhenStatements(rest);
         b = boolOr(b1, b2);
      then b;

    // search deeper inside for
    case (SCode.ALG_WHILE(whileBody = lst)::rest)
      equation
         b1 = containsWhenStatements(lst);
         b2 = containsWhenStatements(rest);
         b  = boolOr(b1, b2);
      then b;

    // not a when, move along
    case (_::rest)
      then containsWhenStatements(rest);
  end matchcontinue;
end containsWhenStatements;

protected function loopOverRange
"@author: adrpo
  Unrolling a for loop is explicitly repeating
  the body of the loop once for each iteration."
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State ci_state;
  input Ident inIdent;
  input Values.Value inValue;
  input list<SCode.Statement> inAlgItmLst;
  input DAE.ElementSource source;
  input SCode.Initial inInitial;
  input Boolean inImpl;
  input Boolean unrollForLoops "we should unroll for loops if they are part of an algorithm in a model";
  output FCore.Cache outCache;
  output list<DAE.Statement> outStatements "for statements can produce more statements than one by unrolling";
algorithm
  (outCache,outStatements) :=
  matchcontinue (inCache,inEnv,inIH,inPrefix,ci_state,inIdent,inValue,inAlgItmLst,source,inInitial,inImpl,unrollForLoops)
    local
      FCore.Graph env_1,env_2,env;
      Prefix.Prefix pre;
      String i;
      Values.Value fst,v;
      list<Values.Value> rest;
      list<SCode.Statement> algs;
      SCode.Initial initial_;
      Boolean impl;
      FCore.Cache cache;
      list<Integer> dims;
      Integer dim;
      list<DAE.Statement> stmts, stmts1, stmts2;
      InstanceHierarchy ih;

    // handle empty
    case (cache,_,_,_,_,_,Values.ARRAY(valueLst = {}),_,_,_,_,_)
      then (cache,{});

    // array equation, use instAlgorithms
    case (cache,env,ih,pre,_,i,Values.ARRAY(valueLst = (fst :: rest), dimLst = dim :: dims),
          algs,_,initial_,impl,_)
      equation
        dim = dim-1;
        dims = dim::dims;
        env_1 = FGraph.openScope(env, SCode.NOT_ENCAPSULATED(), FCore.forScopeName,NONE());
        // the iterator is not constant but the range is constant
        env_2 = FGraph.addForIterator(env_1, i, DAE.T_INTEGER_DEFAULT, DAE.VALBOUND(fst, DAE.BINDING_FROM_DEFAULT_VALUE()), SCode.CONST(), SOME(DAE.C_CONST()));
        /* use instEEquation*/
        (cache,stmts1) = instStatements(cache, env_2, ih, pre, ci_state, algs, source, initial_, impl, unrollForLoops);
        (cache,stmts2) = loopOverRange(cache, env, ih, pre, ci_state, i, Values.ARRAY(rest,dims), algs, source, initial_, impl, unrollForLoops);
        stmts = listAppend(stmts1, stmts2);
      then
        (cache,stmts);

    case (_,_,_,_,_,_,v,_,_,_,_,_)
      equation
        true = Flags.isSet(Flags.FAILTRACE);
        Debug.traceln("- InstSection.loopOverRange failed to loop over range: " + ValuesUtil.valString(v));
      then
        fail();
  end matchcontinue;
end loopOverRange;

protected function rangeExpression "
The function takes a tuple of Absyn.ComponentRef (an array variable) and an integer i
and constructs the range expression (Absyn.Exp) for the ith dimension of the variable"
  input tuple<Absyn.ComponentRef, Integer> inTuple;
  output Absyn.Exp outExp;
algorithm
  outExp := match(inTuple)
    local
      Absyn.Exp e;
      Absyn.ComponentRef acref;
      Integer dimNum;
      tuple<Absyn.ComponentRef, Integer> tpl;

    case ((acref,dimNum))
      equation
        e=Absyn.RANGE(Absyn.INTEGER(1),NONE(),Absyn.CALL(Absyn.CREF_IDENT("size",{}),Absyn.FUNCTIONARGS({Absyn.CREF(acref),Absyn.INTEGER(dimNum)},{})));
      then e;
  end match;
end rangeExpression;

protected function instIfEqBranch
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input list<SCode.EEquation> inEquations;
  input Boolean inImpl;
  output FCore.Cache outCache;
  output FCore.Graph outEnv;
  output InnerOuter.InstHierarchy outIH;
  output ClassInf.State outState;
  output list<DAE.Element> outEquations;
algorithm
  checkForConnectInIfBranch(inEquations);
  (outCache, outEnv, outIH, DAE.DAE(outEquations), outState) :=
    Inst.instList(inCache, inEnv, inIH, inPrefix, inState,
      instEEquation, inEquations, inImpl, alwaysUnroll);
end instIfEqBranch;

protected function instIfEqBranches
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input list<list<SCode.EEquation>> inBranches;
  input Boolean inImpl;
  input list<list<DAE.Element>> inAccumEqs = {};
  output FCore.Cache outCache;
  output FCore.Graph outEnv;
  output InnerOuter.InstHierarchy outIH;
  output ClassInf.State outState;
  output list<list<DAE.Element>> outEquations;
algorithm
  (outCache, outEnv, outIH, outState, outEquations) :=
  match(inCache, inEnv, inIH, inPrefix, inState, inBranches, inImpl, inAccumEqs)
    local
      DAE.Mod mod;
      Prefix.Prefix pre;
      ClassInf.State ci_state,ci_state_1,ci_state_2;
      Boolean impl;
      list<list<DAE.Element>> llb;
      list<list<SCode.EEquation>> es;
      list<SCode.EEquation> e;
      FCore.Cache cache;
      FCore.Graph env;
      InnerOuter.InstHierarchy ih;
      ClassInf.State state;
      list<SCode.EEquation> seq;
      list<list<SCode.EEquation>> rest_seq;
      list<DAE.Element> deq;
      list<list<DAE.Element>> branches;

    case (cache, env, ih, _, state, seq :: rest_seq, _, _)
      equation
        (cache, env, ih, state, deq) =
          instIfEqBranch(cache, env, ih, inPrefix, state, seq, inImpl);
        (cache, env, ih, state, branches) =
          instIfEqBranches(cache, env, ih, inPrefix, state, rest_seq, inImpl, deq :: inAccumEqs);
      then
        (cache, env, ih, state, branches);

    case (_, _, _, _, _, {}, _, _)
      then (inCache, inEnv, inIH, inState, listReverse(inAccumEqs));

  end match;
end instIfEqBranches;

protected function instInitialIfEqBranch
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input list<SCode.EEquation> inEquations;
  input Boolean inImpl;
  output FCore.Cache outCache;
  output FCore.Graph outEnv;
  output InnerOuter.InstHierarchy outIH;
  output ClassInf.State outState;
  output list<DAE.Element> outEquations;
algorithm
  checkForConnectInIfBranch(inEquations);
  (outCache, outEnv, outIH, DAE.DAE(outEquations), outState) :=
    Inst.instList(inCache, inEnv, inIH, inPrefix, inState,
      instEInitialEquation, inEquations, inImpl, alwaysUnroll);
end instInitialIfEqBranch;

protected function instInitialIfEqBranches
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input list<list<SCode.EEquation>> inBranches;
  input Boolean inImpl;
  input list<list<DAE.Element>> inAccumEqs = {};
  output FCore.Cache outCache;
  output FCore.Graph outEnv;
  output InnerOuter.InstHierarchy outIH;
  output ClassInf.State outState;
  output list<list<DAE.Element>> outEquations;
algorithm
  (outCache, outEnv, outIH, outState, outEquations) :=
  match(inCache, inEnv, inIH, inPrefix, inState, inBranches, inImpl, inAccumEqs)
    local
      FCore.Cache cache;
      FCore.Graph env;
      InnerOuter.InstHierarchy ih;
      ClassInf.State state;
      list<SCode.EEquation> seq;
      list<list<SCode.EEquation>> rest_seq;
      list<DAE.Element> deq;
      list<list<DAE.Element>> branches;

    case (cache, env, ih, _, state, seq :: rest_seq, _, _)
      equation
        (cache, env, ih, state, deq) =
          instInitialIfEqBranch(cache, env, ih, inPrefix, state, seq, inImpl);
        (cache, env, ih, state, branches) =
          instInitialIfEqBranches(cache, env, ih, inPrefix, state, rest_seq, inImpl, deq :: inAccumEqs);
      then
        (cache, env, ih, state, branches);

    case (_, _, _, _, _, {}, _, _)
      then (inCache, inEnv, inIH, inState, listReverse(inAccumEqs));

  end match;
end instInitialIfEqBranches;

protected function checkForConnectInIfBranch
  "Checks if an if-branch (a list of equations) contains any connects, and prints
   an error if it does. This is used to check that there are no connects in
   if-equations with non-parameter conditions."
  input list<SCode.EEquation> inEquations;
algorithm
  List.map_0(inEquations, checkForConnectInIfBranch2);
end checkForConnectInIfBranch;

protected function checkForConnectInIfBranch2
  input SCode.EEquation inEquation;
algorithm
  _ := match(inEquation)
    local
      Absyn.ComponentRef cr1, cr2;
      SourceInfo info;
      list<SCode.EEquation> eqs;
      String cr1_str, cr2_str;

    case SCode.EQ_CONNECT(crefLeft = cr1, crefRight = cr2, info = info)
      equation
        cr1_str = Dump.printComponentRefStr(cr1);
        cr2_str = Dump.printComponentRefStr(cr2);
        Error.addSourceMessage(Error.CONNECT_IN_IF, {cr1_str, cr2_str}, info);
      then
        fail();

    case SCode.EQ_FOR(eEquationLst = eqs)
      equation
        checkForConnectInIfBranch(eqs);
      then
        ();

    // No need to recurse into if- or when-equations, they will be checked anyway.
    else ();
  end match;
end checkForConnectInIfBranch2;

protected function instElseIfs
"This function helps instStatement to handle elseif parts."
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPre;
  input ClassInf.State ci_state;
  input list<tuple<Absyn.Exp, list<SCode.Statement>>> inElseIfBranches;
  input DAE.ElementSource source;
  input SCode.Initial initial_;
  input Boolean inImpl;
  input Boolean unrollForLoops "we should unroll for loops if they are part of an algorithm in a model";
  input SourceInfo info;
  output FCore.Cache outCache;
  output list<tuple<DAE.Exp, DAE.Properties, list<DAE.Statement>>> outElseIfBranches;
algorithm
  (outCache,outElseIfBranches) :=
  matchcontinue (inCache,inEnv,inIH,inPre,ci_state,inElseIfBranches,source,initial_,inImpl,unrollForLoops,info)
    local
      FCore.Graph env;
      Boolean impl;
      DAE.Exp e_1,e_2;
      DAE.Properties prop;
      list<DAE.Statement> stmts;
      list<tuple<DAE.Exp, DAE.Properties, list<DAE.Statement>>> tail_1;
      Absyn.Exp e;
      list<SCode.Statement> l;
      list<tuple<Absyn.Exp, list<SCode.Statement>>> tail;
      FCore.Cache cache;
      Prefix.Prefix pre;
      InstanceHierarchy ih;

    case (cache,_,_,_,_,{},_,_,_,_,_) then (cache,{});

    case (cache,env,ih,pre,_,((e,l) :: tail),_,_,impl,_,_)
      equation
        (cache,e_1,prop,_) = Static.elabExp(cache, env, e, impl,NONE(), true,pre,info);
        (cache, e_1, prop) = Ceval.cevalIfConstant(cache, env, e_1, prop, impl, info);
        (cache,e_2) = PrefixUtil.prefixExp(cache, env, ih, e_1, pre);
        (cache,stmts) = instStatements(cache, env, ih, pre, ci_state, l, source, initial_, impl, unrollForLoops);
        (cache,tail_1) = instElseIfs(cache,env,ih,pre,ci_state,tail, source, initial_, impl, unrollForLoops,info);
      then
        (cache,(e_2,prop,stmts) :: tail_1);

    else
      equation
        true = Flags.isSet(Flags.FAILTRACE);
        Debug.trace("- InstSection.instElseIfs failed\n");
      then
        fail();
  end matchcontinue;
end instElseIfs;

protected function instWhenEqBranch
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input tuple<Absyn.Exp, list<SCode.EEquation>> inBranch;
  input Boolean inImpl;
  input Boolean inUnrollLoops;
  input SourceInfo inInfo;
  output FCore.Cache outCache;
  output FCore.Graph outEnv;
  output InnerOuter.InstHierarchy outIH;
  output DAE.Exp outCondition;
  output list<DAE.Element> outEquations;
protected
  Absyn.Exp cond;
  list<SCode.EEquation> body;
  DAE.Properties prop;
algorithm
  (cond, body) := inBranch;

  // Instantiate the when condition.
  (outCache, outCondition) :=
    instExp(inCache, inEnv, inIH, inPrefix, cond, inImpl, inInfo);

  if not Types.isClockOrSubTypeClock(Expression.typeof(outCondition)) then
    List.map_0(body, checkForNestedWhenInEq);
  end if;

  // Instantiate the when body.
  (outCache, outEnv, outIH, DAE.DAE(outEquations), _) :=
    Inst.instList(outCache, inEnv, inIH, inPrefix, inState,
      instEEquation, body, inImpl, alwaysUnroll);
end instWhenEqBranch;

protected function instConnect "
  Generates connectionsets for connections.
  Parameters and constants in connectors should generate appropriate assert statements.
  Hence, a DAE.Element list is returned as well."
  input output FCore.Cache cache;
  input output FCore.Graph env;
  input output InnerOuter.InstHierarchy ih;
  input Prefix.Prefix prefix;
  input Absyn.ComponentRef lhsName;
  input Absyn.ComponentRef rhsName;
  input Boolean implicit;
  input SourceInfo info;
  input DAE.ElementSource source;
        output DAE.DAElist dae;
protected
  Connect.Face face1, face2;
  DAE.Element eq, conn1, conn2;
  Option<DAE.Element> oconn1, oconn2;
  DAE.ElementSource src;
algorithm
  try
    (cache, oconn1, face1) :=
      instConnector(cache, env, ih, lhsName, implicit, prefix, info);
    (cache, oconn2, face2) :=
      instConnector(cache, env, ih, rhsName, implicit, prefix, info);

    // If neither connector is a deleted conditional component, create a
    // connect equation.
    if isNone(oconn1) or isNone(oconn2) then
      dae := DAE.emptyDae;
    else
      SOME(conn1) := oconn1;
      SOME(conn2) := oconn2;
      eq := DAE.CONNECT_EQUATION(conn1, face1, conn2, face2, source);
      dae := DAE.DAE({eq});
    end if;
  else
    true := Flags.isSet(Flags.FAILTRACE);
    Debug.traceln("- InstSection.instConnect failed for: connect(" +
      Dump.printComponentRefStr(lhsName) + ", " +
      Dump.printComponentRefStr(rhsName) + ")");
  end try;
end instConnect;

protected function instConnector
  input output FCore.Cache cache;
  input FCore.Graph env;
  input InnerOuter.InstHierarchy ih;
  input Absyn.ComponentRef connectorCref;
  input Boolean impl;
  input Prefix.Prefix prefix;
  input SourceInfo info;
        output Option<DAE.Element> element;
        output Connect.Face face;
protected
  FCore.Status status;
  Boolean is_expandable, is_outer;
  DAE.Attributes attr;
  DAE.Type ty;
  DAE.ComponentRef cref;
  DAE.VarKind kind;
  DAE.VarDirection dir;
  DAE.VarParallelism par;
  DAE.VarVisibility vis;
  DAE.ConnectorType ct;
  Prefix.Prefix pre = prefix;
algorithm
  cref := ComponentReference.toExpCref(connectorCref);
  (attr, ty, status, is_expandable) := Lookup.lookupConnectorVar(env, cref);

  if FCore.isDeletedComp(status) or is_expandable then
    element := NONE();
    face := Connect.NO_FACE();
  else
    is_outer := Absyn.isOuter(attr.innerOuter);
    (cache, DAE.CREF(componentRef = cref), DAE.PROP(type_ = ty), attr) :=
      Static.elabCrefNoEval(cache, env, connectorCref, impl, false, prefix, info);
    (cache, cref) := Static.canonCref(cache, env, cref, impl);
    validConnector(ty, cref, info);
    ty := sortConnectorType(ty);
    kind := InstUtil.makeDaeVariability(attr.variability);
    dir := InstUtil.makeDaeDirection(attr.direction);
    par := DAE.NON_PARALLEL();
    vis := InstUtil.makeDaeProt(attr.visibility);
    ct := DAEUtil.toConnectorTypeNoState(attr.connectorType);

    if is_outer then
      try
        InnerOuter.INST_INNER(innerPrefix = pre) :=
          InnerOuter.lookupInnerVar(ih, prefix, ComponentReference.crefFirstIdent(cref));
      else
      end try;
    end if;

    face := ConnectUtil.connectorFace(cref);

    (cache, cref) := PrefixUtil.prefixCref(cache, env, ih, pre, cref);
    element := SOME(DAE.VAR(cref, kind, dir, par, vis, ty, NONE(), {}, ct,
      DAE.emptyElementSource, NONE(), NONE(), attr.innerOuter));
  end if;
end instConnector;

protected function sortConnectorType
  input DAE.Type inType;
  output DAE.Type outType;
algorithm
  outType := match(inType)
    local
      DAE.Type ty;
      DAE.Dimensions dims;
      DAE.TypeSource source;
      ClassInf.State ci_state;
      list<DAE.Var> vars;
      DAE.EqualityConstraint ec;

    case DAE.T_ARRAY(ty, dims, source)
      equation
        ty = sortConnectorType(ty);
      then
        DAE.T_ARRAY(ty, dims, source);

    case DAE.T_COMPLEX(ci_state, vars, ec, source)
      equation
        vars = List.sort(vars, connectorCompGt);
      then
        DAE.T_COMPLEX(ci_state, vars, ec, source);

    else inType;

  end match;
end sortConnectorType;

protected function connectorCompGt
  input DAE.Var inVar1;
  input DAE.Var inVar2;
  output Boolean outGt;
protected
  DAE.Ident id1, id2;
algorithm
  DAE.TYPES_VAR(name = id1) := inVar1;
  DAE.TYPES_VAR(name = id2) := inVar2;
  outGt := (1 == stringCompare(id1, id2));
end connectorCompGt;

protected function validConnector
"This function tests whether a type is a eligible to be used in connections."
  input DAE.Type inType;
  input DAE.ComponentRef inCref;
  input SourceInfo inInfo;
algorithm
  _ := matchcontinue inType
    local
      ClassInf.State state;
      DAE.Type tp;
      String str;

    case DAE.T_REAL() then ();
    case DAE.T_INTEGER() then ();
    case DAE.T_STRING() then ();
    case DAE.T_BOOL() then ();
    case DAE.T_ENUMERATION() then ();
    // clocks TODO! FIXME! check if +std=3.3
    case DAE.T_CLOCK() then ();

    case DAE.T_COMPLEX(complexClassType = state)
      equation
        ClassInf.valid(state, SCode.R_CONNECTOR(false));
      then
        ();

    case DAE.T_COMPLEX(complexClassType = state)
      equation
        ClassInf.valid(state, SCode.R_CONNECTOR(true));
      then
        ();

    // TODO, check if subtype is needed here
    case DAE.T_SUBTYPE_BASIC(complexClassType = state)
      equation
        ClassInf.valid(state, SCode.R_CONNECTOR(false));
      then
        ();

    // TODO, check if subtype is needed here
    case DAE.T_SUBTYPE_BASIC(complexClassType = state)
      equation
        ClassInf.valid(state, SCode.R_CONNECTOR(true));
      then
        ();

    case DAE.T_ARRAY(ty = tp)
      equation
        validConnector(tp, inCref, inInfo);
      then
        ();

    // everything in expandable is a connector!
    //case (_, _, _)
    //  equation
    //    true = ConnectUtil.isExpandable(inCref);
    //  then
    //    ();

    else
      equation
        str = ComponentReference.printComponentRefStr(inCref);
        Error.addSourceMessage(Error.INVALID_CONNECTOR_TYPE, {str}, inInfo);
      then
        fail();
  end matchcontinue;
end validConnector;

protected function checkConnectTypes
  input DAE.ComponentRef inLhsCref;
  input DAE.Type inLhsType;
  input Connect.Face inLhsFace;
  input DAE.Attributes inLhsAttributes;
  input DAE.ComponentRef inRhsCref;
  input DAE.Type inRhsType;
  input Connect.Face inRhsFace;
  input DAE.Attributes inRhsAttributes;
  input SourceInfo inInfo;
protected
  SCode.ConnectorType lhs_ct, rhs_ct;
  Absyn.Direction lhs_dir, rhs_dir;
  Absyn.InnerOuter lhs_io, rhs_io;
  SCode.Visibility lhs_vis, rhs_vis;
algorithm
  ComponentReference.checkCrefSubscriptsBounds(inLhsCref, inInfo);
  ComponentReference.checkCrefSubscriptsBounds(inRhsCref, inInfo);
  DAE.ATTR(connectorType = lhs_ct, direction = lhs_dir, innerOuter = lhs_io,
    visibility = lhs_vis) := inLhsAttributes;
  DAE.ATTR(connectorType = rhs_ct, direction = rhs_dir, innerOuter = rhs_io,
    visibility = rhs_vis) := inRhsAttributes;
  checkConnectTypesType(inLhsType, inRhsType, inLhsCref, inRhsCref, inInfo);
  checkConnectTypesFlowStream(lhs_ct, rhs_ct, inLhsCref, inRhsCref, inInfo);
  checkConnectTypesDirection(lhs_dir, inLhsFace, lhs_vis, rhs_dir, inRhsFace,
    rhs_vis, inLhsCref, inRhsCref, inInfo);
  checkConnectTypesInnerOuter(lhs_io, rhs_io, inLhsCref, inRhsCref, inInfo);
end checkConnectTypes;

protected function checkConnectTypesType
  input DAE.Type inLhsType;
  input DAE.Type inRhsType;
  input DAE.ComponentRef inLhsCref;
  input DAE.ComponentRef inRhsCref;
  input SourceInfo inInfo;
algorithm
  _ := matchcontinue(inLhsType, inRhsType, inLhsCref, inRhsCref, inInfo)
    local
      DAE.Type t1, t2;
      String cs1, cs2, cref_str1, cref_str2, str1, str2;
      list<DAE.Dimension> dims1, dims2;

    case (_, _, _, _, _)
      equation
        true = Types.equivtypesOrRecordSubtypeOf(inLhsType, inRhsType);
      then
        ();

    // The type is not identical hence error.
    case (_, _, _, _, _)
      equation
        t1 = Types.arrayElementType(inLhsType);
        t2 = Types.arrayElementType(inRhsType);
        false = Types.equivtypesOrRecordSubtypeOf(t1, t2);
        (_, cs1) = Types.printConnectorTypeStr(t1);
        (_, cs2) = Types.printConnectorTypeStr(t2);
        cref_str1 = ComponentReference.printComponentRefStr(inLhsCref);
        cref_str2 = ComponentReference.printComponentRefStr(inRhsCref);
        Error.addSourceMessage(Error.CONNECT_INCOMPATIBLE_TYPES,
          {cref_str1, cref_str2, cref_str1, cs1, cref_str2, cs2}, inInfo);
      then
        fail();

    // Different dimensionality.
    case (_, _, _, _, _)
      equation
        dims1 = Types.getDimensions(inLhsType);
        dims2 = Types.getDimensions(inRhsType);
        false = List.isEqualOnTrue(dims1, dims2, Expression.dimensionsEqual);
        false = (listLength(dims1) + listLength(dims2)) == 0;
        cref_str1 = ComponentReference.printComponentRefStr(inLhsCref);
        cref_str2 = ComponentReference.printComponentRefStr(inRhsCref);
        str1 = "[" + ExpressionDump.dimensionsString(dims1) + "]";
        str2 = "[" + ExpressionDump.dimensionsString(dims2) + "]";
        Error.addSourceMessage(Error.CONNECTOR_ARRAY_DIFFERENT,
          {cref_str1, cref_str2, str1, str2}, inInfo);
      then
        fail();

  end matchcontinue;
end checkConnectTypesType;

protected function checkConnectTypesFlowStream
  input SCode.ConnectorType inLhsConnectorType;
  input SCode.ConnectorType inRhsConnectorType;
  input DAE.ComponentRef inLhsCref;
  input DAE.ComponentRef inRhsCref;
  input SourceInfo inInfo;
algorithm
  _ := matchcontinue(inLhsConnectorType, inRhsConnectorType, inLhsCref,
      inRhsCref, inInfo)
    local
      String cref_str1, cref_str2, pre_str1, pre_str2;
      list<String> err_strl;

    case (_, _, _, _, _)
      equation
        true = SCode.connectorTypeEqual(inLhsConnectorType, inRhsConnectorType);
      then
        ();

    else
      equation
        cref_str1 = ComponentReference.printComponentRefStr(inLhsCref);
        cref_str2 = ComponentReference.printComponentRefStr(inRhsCref);
        pre_str1 = SCodeDump.connectorTypeStr(inLhsConnectorType);
        pre_str2 = SCodeDump.connectorTypeStr(inRhsConnectorType);
        err_strl = if SCode.potentialBool(inLhsConnectorType)
          then {pre_str2, cref_str2, cref_str1}
          else {pre_str1, cref_str1, cref_str2};
        Error.addSourceMessage(Error.CONNECT_PREFIX_MISMATCH, err_strl, inInfo);
      then
        fail();

  end matchcontinue;
end checkConnectTypesFlowStream;

protected function checkConnectTypesDirection
  input Absyn.Direction inLhsDirection;
  input Connect.Face inLhsFace;
  input SCode.Visibility inLhsVisibility;
  input Absyn.Direction inRhsDirection;
  input Connect.Face inRhsFace;
  input SCode.Visibility inRhsVisibility;
  input DAE.ComponentRef inLhsCref;
  input DAE.ComponentRef inRhsCref;
  input SourceInfo inInfo;
algorithm
  _ := matchcontinue(inLhsDirection, inLhsFace, inLhsVisibility, inRhsDirection,
      inRhsFace, inRhsVisibility, inLhsCref, inRhsCref, inInfo)
    local
      String cref_str1, cref_str2;

    // Two connectors with the same directions but different faces or different
    // directions may be connected.
    case (_, _, _, _, _, _, _, _, _)
      equation
        false = isSignalSource(inLhsDirection, inLhsFace, inLhsVisibility) and
                isSignalSource(inRhsDirection, inRhsFace, inRhsVisibility);
      then
        ();

    else
      equation
        cref_str1 = ComponentReference.printComponentRefStr(inLhsCref);
        cref_str2 = ComponentReference.printComponentRefStr(inRhsCref);
        Error.addSourceMessage(Error.CONNECT_TWO_SOURCES,
          {cref_str1, cref_str2}, inInfo);
      then
        ();

  end matchcontinue;
end checkConnectTypesDirection;

protected function isSignalSource
  input Absyn.Direction inDirection;
  input Connect.Face inFace;
  input SCode.Visibility inVisibility;
  output Boolean outIsSignal;
algorithm
  outIsSignal := match(inDirection, inFace, inVisibility)
    case (Absyn.OUTPUT(), Connect.INSIDE(), _) then true;
    case (Absyn.INPUT(), Connect.OUTSIDE(), SCode.PUBLIC()) then true;
    else false;
  end match;
end isSignalSource;

protected function checkConnectTypesInnerOuter
  input Absyn.InnerOuter inLhsIO;
  input Absyn.InnerOuter inRhsIO;
  input DAE.ComponentRef inLhsCref;
  input DAE.ComponentRef inRhsCref;
  input SourceInfo inInfo;
algorithm
  _ := match(inLhsIO, inRhsIO, inLhsCref, inRhsCref, inInfo)
    local
      String cref_str1, cref_str2;

    case (Absyn.OUTER(), Absyn.OUTER(), _, _, _)
      equation
        cref_str1 = ComponentReference.printComponentRefStr(inLhsCref);
        cref_str2 = ComponentReference.printComponentRefStr(inRhsCref);
        Error.addSourceMessage(Error.CONNECT_OUTER_OUTER,
          {cref_str1, cref_str2}, inInfo);
      then
        fail();

    else ();

  end match;
end checkConnectTypesInnerOuter;

protected function generateConnectAssert
  input DAE.Exp inLhsExp;
  input DAE.Exp inRhsExp;
  input DAE.ElementSource inSource;
  output DAE.Element outAssert;
protected
  DAE.Exp exp;
algorithm
  exp := DAE.RELATION(inLhsExp, DAE.EQUAL(DAE.T_BOOL_DEFAULT), inRhsExp, -1, NONE());
  (exp, _) := ExpressionSimplify.simplify(exp);
  outAssert := DAE.ASSERT(exp, DAE.SCONST("automatically generated from connect"),
    DAE.ASSERTIONLEVEL_ERROR, inSource);
end generateConnectAssert;

protected function expandArrayDimension
  "Expands an array into elements given a dimension, i.e.
    (3, x) => {x[1], x[2], x[3]}"
  input DAE.Dimension inDim;
  input DAE.Exp inArray;
  output list<DAE.Exp> outExpl;
algorithm
  outExpl := matchcontinue(inDim, inArray)
    local
      list<DAE.Exp> expl;
      Integer sz;
      list<Integer> ints;
      Absyn.Path name;
      list<String> ls;

    case (_, DAE.ARRAY(array = outExpl)) then outExpl;

    // Empty integer list. List.intRange is not defined for size < 1,
    // so we need to handle empty lists here.
    case (DAE.DIM_INTEGER(integer = 0), _) then {};
    case (DAE.DIM_INTEGER(integer = sz), _)
      equation
        ints = List.intRange(sz);
        expl = List.map1(ints, makeAsubIndex, inArray);
      then
        expl;
    case (DAE.DIM_BOOLEAN(), _)
      equation
        expl = {ExpressionSimplify.simplify1(Expression.makeASUB(inArray, {DAE.BCONST(false)})),
                ExpressionSimplify.simplify1(Expression.makeASUB(inArray, {DAE.BCONST(true)}))};
      then
        expl;
    case (DAE.DIM_ENUM(enumTypeName = name, literals = ls), _)
      equation
        expl = makeEnumLiteralIndices(name, ls, 1, inArray);
      then
        expl;
    /* adrpo: these are completly wrong!
              will result in equations 1 = 1!
    case (DAE.DIM_EXP(exp = _), _) then {DAE.ICONST(1)};
    case (DAE.DIM_UNKNOWN(), _) then {DAE.ICONST(1)};
    */
    case (DAE.DIM_UNKNOWN(), _)
      equation
        true = Flags.getConfigBool(Flags.CHECK_MODEL);
        ints = List.intRange(1); // try to make an array index of 1 when we don't know the dimension
        expl = List.map1(ints, makeAsubIndex, inArray);
      then
        expl;
  end matchcontinue;
end expandArrayDimension;

protected function makeAsubIndex
  "Creates an ASUB expression given an expression and an integer index."
  input Integer index;
  input DAE.Exp expr;
  output DAE.Exp asub;
algorithm
  (asub,_) := ExpressionSimplify.simplify1(Expression.makeASUB(expr, {DAE.ICONST(index)}));
end makeAsubIndex;

protected function makeEnumLiteralIndices
  "Creates a list of enumeration literal expressions from an enumeration."
  input Absyn.Path enumTypeName;
  input list<String> enumLiterals;
  input Integer enumIndex;
  input DAE.Exp expr;
  output list<DAE.Exp> enumIndices;
algorithm
  enumIndices := match(enumTypeName, enumLiterals, enumIndex, expr)
    local
      String l;
      list<String> ls;
      DAE.Exp e;
      list<DAE.Exp> expl;
      Absyn.Path enum_type_name;
      Integer index;
    case (_, {}, _, _) then {};
    case (_, l :: ls, _, _)
      equation
        enum_type_name = Absyn.joinPaths(enumTypeName, Absyn.IDENT(l));
        e = DAE.ENUM_LITERAL(enum_type_name, enumIndex);
        (e,_) = ExpressionSimplify.simplify1(Expression.makeASUB(expr, {e}));
        e = if Expression.isCref(e) then Expression.unliftExp(e) else e;
        index = enumIndex + 1;
        expl = makeEnumLiteralIndices(enumTypeName, ls, index, expr);
      then
        e :: expl;
  end match;
end makeEnumLiteralIndices;

protected function getVectorizedCref
"for a vectorized cref, return the originial cref without vector subscripts"
input DAE.Exp crefOrArray;
output DAE.Exp cref;
algorithm
   cref := match(crefOrArray)
     local
       DAE.ComponentRef cr;
       DAE.Type t;
       DAE.Exp crefExp;

     case (cref as DAE.CREF(_,_)) then cref;

     case (DAE.ARRAY(_,_,DAE.CREF(cr,t)::_))
       equation
         cr = ComponentReference.crefStripLastSubs(cr);
         crefExp = Expression.makeCrefExp(cr, t);
       then crefExp;
   end match;
end getVectorizedCref;


protected function checkWhenAlgorithm
"@author: adrpo
 checks when equation for:
 - when alg in when alg is not allowed
 - reinit in when with initial condition is not allowed
   when (initial()) then
     reinit(x, y);
   end when;
"
  input SCode.Statement inWhenAlgorithm;
algorithm
  true := checkForReinitInWhenInitialAlg(inWhenAlgorithm);
  checkForNestedWhenInStatements(inWhenAlgorithm);
end checkWhenAlgorithm;

protected function checkForReinitInWhenInitialAlg
  "Fails if a when (initial()) alg contains
   reinit which is not allowed in Modelica."
  input SCode.Statement inWhenAlgorithm;
  output Boolean outOK;
algorithm
  outOK := matchcontinue(inWhenAlgorithm)
    local
      Boolean b1, b2;
      Absyn.Exp exp;
      SourceInfo info;
      list<SCode.Statement> algs;

    // add an error
    case SCode.ALG_WHEN_A(branches = (exp, algs)::_ , info = info)
      equation
        true = Absyn.expContainsInitial(exp);
        true = SCode.algorithmsContainReinit(algs);
        Error.addSourceMessage(Error.REINIT_IN_WHEN_INITIAL, {}, info);
      then false;

    else true;

  end matchcontinue;
end checkForReinitInWhenInitialAlg;

protected function checkForNestedWhenInStatements
  "Fails if a when alg contains nested when
   alg, which are not allowed in Modelica.
   An error message is added when failing."
  input SCode.Statement inWhenAlgorithm;
protected
  list<tuple<Absyn.Exp, list<SCode.Statement>>> branches;
  SourceInfo info;
  list<SCode.Statement> body;
algorithm
  SCode.ALG_WHEN_A(branches = branches, info = info) := inWhenAlgorithm;

  for branch in branches loop
    (_, body) := branch;

    if containsWhenStatements(body) then
      Error.addSourceMessageAndFail(Error.NESTED_WHEN, {}, info);
    end if;
  end for;
end checkForNestedWhenInStatements;

protected function checkWhenEquation
"@author: adrpo
 checks when equation for:
 - when equation in when equation is not allowed
 - reinit in when with initial condition is not allowed
   when (initial()) then
     reinit(x, y);
   end when;"
  input SCode.EEquation inWhenEq;
algorithm
  true := checkForReinitInWhenInitialEq(inWhenEq);
  checkForNestedWhenInEquation(inWhenEq);
end checkWhenEquation;

protected function checkForReinitInWhenInitialEq
  "Fails if a when (initial()) equation contains
   reinit which is not allowed in Modelica."
  input SCode.EEquation inWhenEq;
  output Boolean outOK;
algorithm
  outOK := matchcontinue(inWhenEq)
    local
      Boolean b1, b2;
      Absyn.Exp exp;
      SourceInfo info;
      list<SCode.EEquation> el;
      list<tuple<Absyn.Exp, list<SCode.EEquation>>> tpl_el;

    // Add an error for when initial() then reinit().
    case SCode.EQ_WHEN(condition = exp, eEquationLst = el, info = info)
      equation
        true = Absyn.expContainsInitial(exp);
        true = SCode.equationsContainReinit(el);
        Error.addSourceMessage(Error.REINIT_IN_WHEN_INITIAL, {}, info);
      then
        false;

    else true;

  end matchcontinue;
end checkForReinitInWhenInitialEq;

protected function checkForNestedWhenInEquation
  "Fails if a when equation contains nested when
   equations, which are not allowed in Modelica.
   An error message is added when failing."
  input SCode.EEquation inWhenEq;
algorithm
  _ := match(inWhenEq)
    local
      SourceInfo info;
      list<SCode.EEquation> eqs;
      list<list<SCode.EEquation>> eqs_lst;
      list<tuple<Absyn.Exp, list<SCode.EEquation>>> tpl_el;

    // continue if when equations are not nested
    case SCode.EQ_WHEN(eEquationLst = eqs, elseBranches = tpl_el)
      equation
        checkForNestedWhenInEqList(eqs);
        eqs_lst = List.map(tpl_el, Util.tuple22);
        List.map_0(eqs_lst, checkForNestedWhenInEqList);
      then
        ();

  end match;
end checkForNestedWhenInEquation;

protected function checkForNestedWhenInEqList
  "Helper function to checkForNestedWhen. Searches for nested when equations in
  a list of equations."
  input list<SCode.EEquation> inEqs;
algorithm
  List.map_0(inEqs, checkForNestedWhenInEq);
end checkForNestedWhenInEqList;

protected function checkForNestedWhenInEq
  "Helper function to checkForNestedWhen. Searches for nested when equations in
  an equation."
  input SCode.EEquation inEq;
algorithm
  _ := match(inEq)
    local
      list<SCode.EEquation> eqs;
      list<list<SCode.EEquation>> eqs_lst;
      Absyn.ComponentRef cr1, cr2;
      SourceInfo info;
      String cr1_str, cr2_str;

    case SCode.EQ_WHEN(info = info)
      equation
        Error.addSourceMessage(Error.NESTED_WHEN, {}, info);
      then
        fail();

    case SCode.EQ_IF(thenBranch = eqs_lst, elseBranch = eqs)
      equation
        List.map_0(eqs_lst, checkForNestedWhenInEqList);
        checkForNestedWhenInEqList(eqs);
      then
        ();

    case SCode.EQ_FOR(eEquationLst = eqs)
      equation
        checkForNestedWhenInEqList(eqs);
      then
        ();

    case SCode.EQ_EQUALS() then ();
    case SCode.EQ_PDE() then ();

    // connect is not allowed in when equations.
    case SCode.EQ_CONNECT(crefLeft = cr1, crefRight = cr2, info = info)
      equation
        cr1_str = Dump.printComponentRefStr(cr1);
        cr2_str = Dump.printComponentRefStr(cr2);
        Error.addSourceMessage(Error.CONNECT_IN_WHEN, {cr1_str, cr2_str}, info);
      then
        fail();

    case SCode.EQ_ASSERT() then ();
    case SCode.EQ_TERMINATE() then ();
    case SCode.EQ_REINIT() then ();
    case SCode.EQ_NORETCALL() then ();

    case _
      equation
        true = Flags.isSet(Flags.FAILTRACE);
        Debug.trace("- InstSection.checkForNestedWhenInEq failed.\n");
      then
        fail();

  end match;
end checkForNestedWhenInEq;

protected function instAssignment
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy ih;
  input Prefix.Prefix inPre;
  input SCode.Statement alg;
  input DAE.ElementSource source;
  input SCode.Initial initial_;
  input Boolean impl;
  input Boolean unrollForLoops "we should unroll for loops if they are part of an algorithm in a model";
  input Integer numError;
  output FCore.Cache outCache;
  output list<DAE.Statement> stmts "more statements due to loop unrolling";
algorithm
  (outCache,stmts) := matchcontinue (inCache,inEnv,ih,inPre,alg,source,initial_,impl,unrollForLoops,numError)
    local
      FCore.Cache cache;
      FCore.Graph env;
      DAE.Exp e_1;
      DAE.Properties eprop;
      Prefix.Prefix pre;
      Absyn.Exp var;
      Absyn.Exp value;
      SourceInfo info;
      String str;
      DAE.Type t;

    case (cache,env,_,pre,SCode.ALG_ASSIGN(assignComponent=var,value=value,info=info),_,_,_,_,_)
      equation
        (cache,e_1,eprop,_) = Static.elabExp(cache,env,value,impl,NONE(),true,pre,info);
        (cache,stmts) = instAssignment2(cache,env,ih,pre,var,value,e_1,eprop,info,ElementSource.addAnnotation(source, alg.comment),initial_,impl,unrollForLoops,numError);
      then (cache,stmts);

    case (cache,env,_,pre,SCode.ALG_ASSIGN(value=value,info=info),_,_,_,_,_)
      equation
        true = numError == Error.getNumErrorMessages();
        failure((_,_,_,_) = Static.elabExp(cache,env,value,impl,NONE(),true,pre,info));
        str = Dump.unparseAlgorithmStr(SCode.statementToAlgorithmItem(alg));
        Error.addSourceMessage(Error.ASSIGN_RHS_ELABORATION,{str},info);
      then fail();
  end matchcontinue;
end instAssignment;

protected function instAssignment2
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPre;
  input Absyn.Exp var;
  input Absyn.Exp inRhs;
  input DAE.Exp value;
  input DAE.Properties props;
  input SourceInfo info;
  input DAE.ElementSource inSource;
  input SCode.Initial initial_;
  input Boolean inImpl;
  input Boolean unrollForLoops "we should unroll for loops if they are part of an algorithm in a model";
  input Integer numError;
  output FCore.Cache outCache;
  output list<DAE.Statement> stmts "more statements due to loop unrolling";
algorithm
  (outCache,stmts) := matchcontinue (inCache,var,value,props)
    local
      DAE.ComponentRef ce,ce_1;
      DAE.Properties cprop,eprop,prop,prop1,prop2;
      DAE.Exp e_1, e_2, cre, cre2, e2_2, e2_2_2, lhs, rhs;
      DAE.Statement stmt;
      Absyn.ComponentRef cr;
      Absyn.Exp e,e1,e2, left;
      list<Absyn.Exp> expl;
      list<DAE.Exp> expl_1,expl_2;
      list<DAE.Properties> cprops, eprops;
      list<DAE.Attributes> attrs;
      DAE.Type lt,rt,ty,t;
      String s,lhs_str,rhs_str,lt_str,rt_str,s1,s2;
      FCore.Cache cache;
      DAE.Pattern pattern;
      DAE.Attributes attr;
      DAE.ElementSource source;
      DAE.Dimension dim, lhs_dim, rhs_dim;
      list<DAE.Exp> lhs_idxs, rhs_idxs;

    // v := expr; where v or expr are size 0
    case (cache,Absyn.CREF(cr),e_1,_)
      equation
        (cache,lhs as DAE.CREF(_,t),_,attr) =
          Static.elabCrefNoEval(cache, inEnv, cr, inImpl, false, inPre, info);
        DAE.T_ARRAY( dims = {_}) = t;
        rhs = e_1;
        Static.checkAssignmentToInput(var, attr, inEnv, false, info);
        DAE.T_ARRAY(dims = lhs_dim :: _) = Expression.typeof(lhs);
        DAE.T_ARRAY(dims = rhs_dim :: _) = Expression.typeof(rhs);
        {} = expandArrayDimension(lhs_dim, lhs);
        {} = expandArrayDimension(rhs_dim, rhs);
      then
        (cache,{});

    // v := expr;
    case (cache,Absyn.CREF(cr),e_1,eprop)
      equation
        (cache,DAE.CREF(ce,t),cprop,attr) =
          Static.elabCrefNoEval(cache, inEnv, cr, inImpl, false, inPre, info);
        Static.checkAssignmentToInput(var, attr, inEnv, false, info);
        (cache, ce_1) = Static.canonCref(cache, inEnv, ce, inImpl);
        (cache, ce_1) = PrefixUtil.prefixCref(cache, inEnv, inIH, inPre, ce_1);

        (cache, t) = PrefixUtil.prefixExpressionsInType(cache, inEnv, inIH, inPre, t);

        lt = Types.getPropType(cprop);
        (cache, lt) = PrefixUtil.prefixExpressionsInType(cache, inEnv, inIH, inPre, lt);
        cprop = Types.setPropType(cprop, lt);

        (cache, e_1, eprop) = Ceval.cevalIfConstant(cache, inEnv, e_1, eprop, inImpl, info);
        (cache, e_2) = PrefixUtil.prefixExp(cache, inEnv, inIH, e_1, inPre);

        rt = Types.getPropType(eprop);
        (cache, rt) = PrefixUtil.prefixExpressionsInType(cache, inEnv, inIH, inPre, rt);
        eprop = Types.setPropType(eprop, rt);

        source = ElementSource.addElementSourceFileInfo(inSource, info);
        stmt = makeAssignment(Expression.makeCrefExp(ce_1,t), cprop, e_2, eprop, attr, initial_, source);
      then
        (cache,{stmt});

    // der(x) := ...
    case (cache,e2 as Absyn.CALL(function_ = Absyn.CREF_IDENT(name="der"),functionArgs=(Absyn.FUNCTIONARGS(args={Absyn.CREF(cr)})) ),e_1,eprop)
      equation
        (cache,_,cprop,attr) =
          Static.elabCrefNoEval(cache,inEnv, cr, inImpl,false,inPre,info);
        (cache,(e2_2 as DAE.CALL()),_,_) =
          Static.elabExp(cache,inEnv, e2, inImpl,NONE(),true,inPre,info);
        (cache,e2_2_2) = PrefixUtil.prefixExp(cache, inEnv, inIH, e2_2, inPre);
        (cache, e_1, eprop) = Ceval.cevalIfConstant(cache, inEnv, e_1, eprop, inImpl, info);
        (cache,e_2) = PrefixUtil.prefixExp(cache, inEnv, inIH, e_1, inPre);
        source = ElementSource.addElementSourceFileInfo(inSource, info);
        stmt = makeAssignment(e2_2_2, cprop, e_2, eprop, attr /*SCode.RW()*/, initial_, source);
      then
        (cache,{stmt});

    // v[i] := expr (in e.g. for loops)
    case (cache,Absyn.CREF(cr),e_1,eprop)
      equation
        (cache,cre,cprop,attr) =
          Static.elabCrefNoEval(cache,inEnv, cr, inImpl,false,inPre,info);
        Static.checkAssignmentToInput(var, attr, inEnv, false, info);
        (cache,cre2) = PrefixUtil.prefixExp(cache, inEnv, inIH, cre, inPre);
        (cache, e_1, eprop) = Ceval.cevalIfConstant(cache, inEnv, e_1, eprop, inImpl, info);
        (cache,e_2) = PrefixUtil.prefixExp(cache, inEnv, inIH, e_1, inPre);
        source = ElementSource.addElementSourceFileInfo(inSource, info);
        stmt = makeAssignment(cre2, cprop, e_2, eprop, attr, initial_, source);
      then
        (cache,{stmt});

    // (v1,v2,..,vn) := func(...)
    case (cache,Absyn.TUPLE(expressions = expl),e_1,eprop)
      equation
        true = List.all(expl, Absyn.isCref);
        (cache, e_1 as DAE.CALL(), eprop) = Ceval.cevalIfConstant(cache, inEnv, e_1, eprop, inImpl, info);
        (cache,e_2) = PrefixUtil.prefixExp(cache, inEnv, inIH, e_1, inPre);
        (cache,expl_1,cprops,attrs,_) =
          Static.elabExpCrefNoEvalList(cache, inEnv, expl, inImpl, NONE(), false, inPre, info);
        Static.checkAssignmentToInputs(expl, attrs, inEnv, info);
        checkNoDuplicateAssignments(expl_1, info);
        (cache,expl_2) = PrefixUtil.prefixExpList(cache, inEnv, inIH, expl_1, inPre);
        source = ElementSource.addElementSourceFileInfo(inSource, info);
        stmt = Algorithm.makeTupleAssignment(expl_2, cprops, e_2, eprop, initial_, source);
      then
        (cache,{stmt});

    // (v1,v2,..,vn) := match...
    case (cache,Absyn.TUPLE(expressions = expl),e_1,eprop)
      equation
        true = Config.acceptMetaModelicaGrammar();
        true = List.all(expl, Absyn.isCref);
        true = Types.isTuple(Types.getPropType(eprop));
        (cache, e_1 as DAE.MATCHEXPRESSION(), eprop) = Ceval.cevalIfConstant(cache, inEnv, e_1, eprop, inImpl, info);
        (cache,e_2) = PrefixUtil.prefixExp(cache, inEnv, inIH, e_1, inPre);
        (cache,expl_1,cprops,attrs,_) =
          Static.elabExpCrefNoEvalList(cache, inEnv, expl, inImpl, NONE(), false, inPre, info);
        Static.checkAssignmentToInputs(expl, attrs, inEnv, info);
        checkNoDuplicateAssignments(expl_1, info);
        (cache,expl_2) = PrefixUtil.prefixExpList(cache, inEnv, inIH, expl_1, inPre);
        source = ElementSource.addElementSourceFileInfo(inSource, info);
        stmt = Algorithm.makeTupleAssignment(expl_2, cprops, e_2, eprop, initial_, source);
      then
        (cache,{stmt});

    case (cache,left,e_1,prop)
      equation
        true = Config.acceptMetaModelicaGrammar();
        ty = Types.getPropType(prop);
        (e_1,ty) = Types.convertTupleToMetaTuple(e_1,ty);
        (cache,pattern) = Patternm.elabPatternCheckDuplicateBindings(cache,inEnv,left,ty,info);
        source = ElementSource.addElementSourceFileInfo(inSource, info);
        stmt = if Types.isEmptyOrNoRetcall(ty) then DAE.STMT_NORETCALL(e_1,source) else DAE.STMT_ASSIGN(DAE.T_UNKNOWN_DEFAULT,DAE.PATTERN(pattern),e_1,source);
      then (cache,{stmt});

    /* Tuple with rhs constant */
    case (cache,Absyn.TUPLE(expressions = expl),e_1,eprop)
      equation
        (cache, e_1 as DAE.TUPLE(PR = expl_1), eprop) = Ceval.cevalIfConstant(cache, inEnv, e_1, eprop, inImpl, info);
        (cache,expl_2,cprops,attrs,_) =
          Static.elabExpCrefNoEvalList(cache,inEnv, expl, inImpl,NONE(),false,inPre,info);
        Static.checkAssignmentToInputs(expl, attrs, inEnv, info);
        checkNoDuplicateAssignments(expl_2, info);
        (cache,expl_2) = PrefixUtil.prefixExpList(cache, inEnv, inIH, expl_2, inPre);
        eprops = Types.propTuplePropList(eprop);
        source = ElementSource.addElementSourceFileInfo(inSource, info);
        stmts = Algorithm.makeAssignmentsList(expl_2, cprops, expl_1, eprops, /* SCode.RW() */ DAE.dummyAttrVar, initial_, source);
      then
        (cache,stmts);

    /* Tuple with lhs being a tuple NOT of crefs => Error */
    case (_,e as Absyn.TUPLE(expressions = expl),_,_)
      equation
        false = List.all(expl, Absyn.isCref);
        s = Dump.printExpStr(e);
        Error.addSourceMessage(Error.TUPLE_ASSIGN_CREFS_ONLY, {s}, info);
      then
        fail();

    case (cache,e1 as Absyn.TUPLE(expressions = expl),e_2,prop2)
      equation
        Absyn.CALL() = inRhs;
        true = List.all(expl, Absyn.isCref);
        (cache,e_1,prop1,_) = Static.elabExp(cache,inEnv,e1,inImpl,NONE(),false,inPre,info);
        lt = Types.getPropType(prop1);
        rt = Types.getPropType(prop2);
        false = Types.subtype(lt, rt);
        lhs_str = ExpressionDump.printExpStr(e_1);
        rhs_str = Dump.printExpStr(inRhs);
        lt_str = Types.unparseTypeNoAttr(lt);
        rt_str = Types.unparseTypeNoAttr(rt);
        Types.typeErrorSanityCheck(lt_str, rt_str, info);
        Error.addSourceMessage(Error.ASSIGN_TYPE_MISMATCH_ERROR,{lhs_str,rhs_str,lt_str,rt_str}, info);
      then
        fail();

    /* Tuple with rhs not CALL or CONSTANT => Error */
    case (_,Absyn.TUPLE(expressions = expl),e_1,_)
      equation
        true = List.all(expl, Absyn.isCref);
        failure(Absyn.CALL() = inRhs);
        s = ExpressionDump.printExpStr(e_1);
        Error.addSourceMessage(Error.TUPLE_ASSIGN_FUNCALL_ONLY, {s}, info);
      then
        fail();

    else
      equation
        true = numError == Error.getNumErrorMessages();
        s1 = Dump.printExpStr(var);
        s2 = ExpressionDump.printExpStr(value);
        Error.addSourceMessage(Error.ASSIGN_UNKNOWN_ERROR, {s1,s2}, info);
      then
        fail();
  end matchcontinue;
end instAssignment2;

function checkNoDuplicateAssignments
  input list<DAE.Exp> inExps;
  input SourceInfo info;
protected
  DAE.Exp exp;
  list<DAE.Exp> exps=inExps;
algorithm
  while not listEmpty(exps) loop
    exp::exps := exps;
    if Expression.isWild(exp) then
      continue;
    elseif listMember(exp, exps) then
      Error.addSourceMessage(Error.DUPLICATE_DEFINITION, {ExpressionDump.printExpStr(exp)}, info);
      fail();
    end if;
  end while;
end checkNoDuplicateAssignments;

protected function generateNoConstantBindingError
  input Option<Values.Value> emptyValueOpt;
  input SourceInfo info;
algorithm
  _ := match(emptyValueOpt, info)
    local
      String scope "the scope where we could not find the binding";
      String name "the name of the variable";
      Values.Value ty "the DAE.Type translated to Value using defaults";
      String tyStr "the type of the variable";

    case (NONE(), _) then ();
    case (SOME(Values.EMPTY(scope, name, _, _)), _)
      equation
         Error.addSourceMessage(Error.NO_CONSTANT_BINDING, {name, scope}, info);
      then
        fail();

  end match;
end generateNoConstantBindingError;

protected function getIteratorType
  input DAE.Type ty;
  input String id;
  input SourceInfo info;
  output DAE.Type oty;
algorithm
  oty := match ty
    local
      String str;
    case DAE.T_ARRAY(ty = DAE.T_ARRAY())
      equation
        str = Types.unparseType(ty);
        Error.addSourceMessage(Error.ITERATOR_NON_ARRAY,{id,str},info);
      then fail();
    case DAE.T_ARRAY(ty = oty) then oty;
    case DAE.T_METALIST(ty = oty) then Types.boxIfUnboxedType(oty);
    case DAE.T_METAARRAY(ty = oty) then Types.boxIfUnboxedType(oty);
    case DAE.T_METATYPE(ty = oty) then getIteratorType(ty.ty, id, info);
    else
      equation
        str = Types.unparseType(ty);
        Error.addSourceMessage(Error.ITERATOR_NON_ARRAY,{id,str},info);
      then fail();
  end match;
end getIteratorType;

protected function instParForStatement
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input SCode.Statement inForStatement;
  input DAE.ElementSource inSource;
  input SCode.Initial inInitial;
  input Boolean inImpl;
  input Boolean inUnrollLoops;
  output FCore.Cache outCache;
  output list<DAE.Statement> outStatements "For statements can produce multiple statements due to unrolling.";
protected
  String iterator;
  Option<Absyn.Exp> oarange;
  Absyn.Exp arange;
  DAE.Exp range;
  DAE.Properties prop;
  list<SCode.Statement> body;
  SourceInfo info;
  list<Absyn.IteratorIndexedCref> iter_crefs;
algorithm
  SCode.ALG_PARFOR(index = iterator, range = oarange, parforBody = body, info = info) := inForStatement;

  if isSome(oarange) then
    SOME(arange) := oarange;
    (outCache, range, prop) :=
      Static.elabExp(inCache, inEnv, arange, inImpl, NONE(), true, inPrefix, info);
  else
    iter_crefs := SCode.findIteratorIndexedCrefsInStatements(body, iterator);
    (range, prop, outCache) :=
      Static.deduceIterationRange(iterator, iter_crefs, inEnv, inCache, info);
  end if;

  // Always unroll for-loops containing when-statements.
  if containsWhenStatements(body) then
    (outCache, outStatements) := unrollForLoop(inCache, inEnv, inIH, inPrefix,
      inState, iterator, range, prop, body, inForStatement, info, inSource,
      inInitial, inImpl, inUnrollLoops);
  else
    (outCache, outStatements) := instParForStatement_dispatch(inCache, inEnv, inIH,
      inPrefix, inState, iterator, range, prop, body, info, inSource, inInitial, inImpl, inUnrollLoops);
  end if;
end instParForStatement;

protected function instParForStatement_dispatch
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
  input InnerOuter.InstHierarchy inIH;
  input Prefix.Prefix inPrefix;
  input ClassInf.State inState;
  input String inIterator;
  input DAE.Exp inRange;
  input DAE.Properties inRangeProps;
  input list<SCode.Statement> inBody;
  input SourceInfo inInfo;
  input DAE.ElementSource inSource;
  input SCode.Initial inInitial;
  input Boolean inImpl;
  input Boolean inUnrollLoops;
  output FCore.Cache outCache = inCache;
  output list<DAE.Statement> outStatements;
protected
  DAE.Type ty;
  DAE.Const c;
  FCore.Graph env;
  DAE.ElementSource source;
  list<tuple<DAE.ComponentRef, SourceInfo>> loop_prl_vars;
  DAE.ComponentRef parfor_iter;
  DAE.Exp range;
algorithm
  c := Types.getPropConst(inRangeProps);

  // Remove the for-loop if the range is empty.
  if Types.isParameterOrConstant(c) then
    try
      (outCache, Values.ARRAY(valueLst = {}), _) :=
        Ceval.ceval(outCache, inEnv, inRange, inImpl, NONE(), Absyn.MSG(inInfo), 0);
      outStatements := {};
      return;
    else
    end try;
  end if;

  ty := Types.getPropType(inRangeProps);
  ty := getIteratorType(ty, inIterator, inInfo);
  (outCache, range) :=
    Ceval.cevalRangeIfConstant(outCache, inEnv, inRange, inRangeProps, inImpl, inInfo);
  (outCache, range) := PrefixUtil.prefixExp(outCache, inEnv, inIH, range, inPrefix);
  env := addParForLoopScope(inEnv, inIterator, ty, SCode.VAR(), SOME(c));
  (outCache, outStatements) := instStatements(outCache, env, inIH, inPrefix,
    inState, inBody, inSource, inInitial, inImpl, inUnrollLoops);

  // this is where we check the parfor loop for data parallel specific
  // situations. Start with empty list and collect all variables cref'ed
  // in the loop body.
  loop_prl_vars := collectParallelVariables({}, outStatements);

  // Remove the parfor loop iterator from the list(implicitly declared).
  parfor_iter := DAE.CREF_IDENT(inIterator, ty, {});
  loop_prl_vars := List.deleteMemberOnTrue(parfor_iter, loop_prl_vars, crefInfoListCrefsEqual);

  // Check the cref's in the list one by one to make
  // sure that they are parallel variables.
  // checkParallelVariables(cache,env_1,loopPrlVars);
  List.map2_0(loop_prl_vars, isCrefParGlobalOrForIterator, outCache, env);

  source := ElementSource.addElementSourceFileInfo(inSource, inInfo);
  outStatements :=
    {Algorithm.makeParFor(inIterator, range, inRangeProps, outStatements, loop_prl_vars, source)};
end instParForStatement_dispatch;

protected function isCrefParGlobalOrForIterator
"Checks if a component reference is referencing a parglobal
variable or the loop iterator(implicitly declared is OK).
All other references are errors."
  input tuple<DAE.ComponentRef,SourceInfo> inCrefInfo;
  input FCore.Cache inCache;
  input FCore.Graph inEnv;
algorithm
  _ := matchcontinue(inCrefInfo,inCache,inEnv)
    local
      String errorString;
      DAE.ComponentRef cref;
      SourceInfo info;
      SCode.Parallelism prl;
      Boolean isParglobal;
      Option<DAE.Const> cnstForRange;

    case((cref,_),_,_)
      equation
        // Look up the variable
        (_, DAE.ATTR(parallelism = prl),_,_,_,_,_,_,_) = Lookup.lookupVar(inCache, inEnv, cref);

        // is it parglobal var?
        isParglobal = SCode.parallelismEqual(prl, SCode.PARGLOBAL());

        // Now the iterator is already removed. No need for this.
        // is it the iterator of the parfor loop(implicitly declared)?
        // isForiterator = isSome(cnstForRange);

        //is it either a parglobal var or for iterator
        //true = isParglobal or isForiterator;

        true = isParglobal;

      then ();

    case((cref,info),_,_)
      equation
        errorString = "\n" +
        "- Component '" + Absyn.pathString(ComponentReference.crefToPath(cref)) +
        "' is used in a parallel for loop." + "\n" +
        "- Parallel for loops can only contain references to parglobal variables."
        ;
        Error.addSourceMessage(Error.PARMODELICA_ERROR,
          {errorString}, info);
      then fail();

  end matchcontinue;
end isCrefParGlobalOrForIterator;


protected function crefInfoListCrefsEqual
"Compares if two <DAE.ComponentRef,SourceInfo> tuples have
are the same in the sense that they have the same cref (which
means they are references to the same component).
The info is
just for error messages."
  input DAE.ComponentRef inFoundCref;
  input tuple<DAE.ComponentRef,SourceInfo> inCrefInfos;
  output Boolean outBoolean;
algorithm
  outBoolean := match(inFoundCref,inCrefInfos)
  local
    DAE.ComponentRef cref1;

    case(_,(cref1,_)) then ComponentReference.crefEqualWithoutSubs(cref1,inFoundCref);
  end match;
end crefInfoListCrefsEqual;


protected function collectParallelVariables
"Traverses the body of a parallel for loop and collects
all variable references. the list should not include implictly
declared variables like loop iterators. Only references to
components declared to outside of the parfor loop need to be
collected.
We need the list of referenced variables for Code generation in the backend.
EXPENSIVE operation but needs to be done."
  input list<tuple<DAE.ComponentRef,SourceInfo>> inCrefInfos;
  input list<DAE.Statement> inStatments;
  output list<tuple<DAE.ComponentRef,SourceInfo>> outCrefInfos;

algorithm
  outCrefInfos := matchcontinue(inCrefInfos,inStatments)
    local
      list<DAE.Statement> restStmts, stmtList;
      list<tuple<DAE.ComponentRef,SourceInfo>> crefInfoList;
      DAE.ComponentRef foundCref;
      DAE.Exp exp1,exp2;
      SourceInfo info;
      DAE.Ident iter;
      DAE.Type iterType;
      DAE.Statement debugStmt;

    case(_,{}) then inCrefInfos;

    case(crefInfoList,DAE.STMT_ASSIGN(_, exp1, exp2, DAE.SOURCE(info = info))::restStmts)
      equation
        //check the lhs and rhs.
        crefInfoList = collectParallelVariablesinExps(crefInfoList,{exp1,exp2},info);

        //check the rest
        crefInfoList = collectParallelVariables(crefInfoList,restStmts);
      then crefInfoList;

    // for statment
    case(crefInfoList, DAE.STMT_FOR(type_=iterType, iter=iter, range=exp1, statementLst=stmtList, source=DAE.SOURCE(info = info))::restStmts)
      equation
        //check the range exp.
        crefInfoList = collectParallelVariablesinExps(crefInfoList,{exp1},info);

        // check the body of the loop.
//        crefInfoList_tmp = collectParallelVariables(crefInfoList,stmtList);
        crefInfoList = collectParallelVariables(crefInfoList,stmtList);
        // We need to remove the iterator from
        // the list generated for the loop bofy. For iterators are implicitly declared.
        // This should be done here since the iterator is in scope only as long as we
        // are in the loop body.
        foundCref = DAE.CREF_IDENT(iter, iterType,{});
        // (crefInfoList_tmp,_) = List.deleteMemberOnTrue(foundCref,crefInfoList_tmp,crefInfoListCrefsEqual);
        (crefInfoList,_) = List.deleteMemberOnTrue(foundCref,crefInfoList,crefInfoListCrefsEqual);

        // Now that the iterator is removed cocatenate the two lists
        // crefInfoList = listAppend(expandableEqs(crefInfoList_tmp,crefInfoList);

        //check the rest
        crefInfoList = collectParallelVariables(crefInfoList,restStmts);
      then crefInfoList;

    // If statment
    // mahge TODO: Fix else Exps.
    case(crefInfoList, DAE.STMT_IF(exp1, stmtList, _, DAE.SOURCE(info = info))::restStmts)
      equation
        //check the condition exp.
        crefInfoList = collectParallelVariablesinExps(crefInfoList,{exp1},info);
        //check the body of the if statment
        crefInfoList = collectParallelVariables(crefInfoList,stmtList);

        //check the rest
        crefInfoList = collectParallelVariables(crefInfoList,restStmts);
      then crefInfoList;

    case(crefInfoList, DAE.STMT_WHILE(exp1, stmtList, DAE.SOURCE(info = info))::restStmts)
      equation
        //check the condition exp.
        crefInfoList = collectParallelVariablesinExps(crefInfoList,{exp1},info);
        //check the body of the while loop
        crefInfoList = collectParallelVariables(crefInfoList,stmtList);

        //check the rest
        crefInfoList = collectParallelVariables(crefInfoList,restStmts);
      then crefInfoList;

    case(crefInfoList,_::restStmts)
      then collectParallelVariables(crefInfoList,restStmts);

  end matchcontinue;
end collectParallelVariables;



protected function collectParallelVariablesinExps
  input list<tuple<DAE.ComponentRef,SourceInfo>> inCrefInfos;
  input list<DAE.Exp> inExps;
  input SourceInfo inInfo;
  output list<tuple<DAE.ComponentRef,SourceInfo>> outCrefInfos;

algorithm
  outCrefInfos := matchcontinue(inCrefInfos,inExps,inInfo)
    local
      list<DAE.Exp> restExps;
      list<tuple<DAE.ComponentRef,SourceInfo>> crefInfoList;
      DAE.ComponentRef foundCref;
      DAE.Exp exp1,exp2,exp3;
      list<DAE.Exp> expLst1;
      list<DAE.Subscript> subscriptLst;
      Boolean alreadyInList;
      DAE.Exp debugExp;


    case(_,{},_) then inCrefInfos;

    case(crefInfoList,DAE.CREF(foundCref, _)::restExps,_)
      equation
        // Check if the cref is already added to the list
        // avoid repeated lookup.
        // and we don't care about subscript differences.

        alreadyInList = List.isMemberOnTrue(foundCref,crefInfoList,crefInfoListCrefsEqual);

        // add it to the list if it is not in there
        crefInfoList = if alreadyInList then crefInfoList else ((foundCref,inInfo)::crefInfoList);

        //check the subscripts (that is: if they are crefs)
        DAE.CREF_IDENT(_,_,subscriptLst) = foundCref;
        crefInfoList = collectParallelVariablesInSubscriptList(crefInfoList,subscriptLst,inInfo);

        // check the rest
        crefInfoList = collectParallelVariablesinExps(crefInfoList,restExps,inInfo);
      then crefInfoList;

    // Array subscripting
    case(crefInfoList, DAE.ASUB(exp1,expLst1)::restExps,_)
      equation
        //check the ASUB specific expressions
        crefInfoList = collectParallelVariablesinExps(crefInfoList,exp1::expLst1,inInfo);

        // check the rest
        crefInfoList = collectParallelVariablesinExps(crefInfoList,restExps,inInfo);
      then crefInfoList;

    // Binary Operations
    case(crefInfoList, DAE.BINARY(exp1,_, exp2)::restExps,_)
      equation
        //check the lhs and rhs
        crefInfoList = collectParallelVariablesinExps(crefInfoList,{exp1,exp2},inInfo);

        // check the rest
        crefInfoList = collectParallelVariablesinExps(crefInfoList,restExps,inInfo);
      then crefInfoList;

    // Unary Operations
    case(crefInfoList, DAE.UNARY(_, exp1)::restExps,_)
      equation
        //check the exp
        crefInfoList = collectParallelVariablesinExps(crefInfoList,{exp1},inInfo);

        // check the rest
        crefInfoList = collectParallelVariablesinExps(crefInfoList,restExps,inInfo);
      then crefInfoList;

    // Logical Binary Operations
    case(crefInfoList, DAE.LBINARY(exp1,_, exp2)::restExps,_)
      equation
        //check the lhs and rhs
        crefInfoList = collectParallelVariablesinExps(crefInfoList,{exp1,exp2},inInfo);

        // check the rest
        crefInfoList = collectParallelVariablesinExps(crefInfoList,restExps,inInfo);
      then crefInfoList;

    // Logical Unary Operations
    case(crefInfoList, DAE.LUNARY(_, exp1)::restExps,_)
      equation
        //check the exp
        crefInfoList = collectParallelVariablesinExps(crefInfoList,{exp1},inInfo);

        // check the rest
        crefInfoList = collectParallelVariablesinExps(crefInfoList,restExps,inInfo);
      then crefInfoList;

    // range with step value.
    case(crefInfoList, DAE.RANGE(_, exp1, SOME(exp2), exp3)::restExps,_)
      equation
        //check the range specific expressions
        crefInfoList = collectParallelVariablesinExps(crefInfoList,{exp1,exp2,exp3},inInfo);

        // check the rest
        crefInfoList = collectParallelVariablesinExps(crefInfoList,restExps,inInfo);
      then crefInfoList;

    // range withOUT step value.
    case(crefInfoList, DAE.RANGE(_, exp1, NONE(), exp3)::restExps,_)
      equation
        //check the range specific expressions
        crefInfoList = collectParallelVariablesinExps(crefInfoList,{exp1,exp3},inInfo);

        // check the rest
        crefInfoList = collectParallelVariablesinExps(crefInfoList,restExps,inInfo);
      then crefInfoList;

    // cast stmt
    case(crefInfoList, DAE.CAST(_, exp1)::restExps,_)
      equation
        //check the range specific expressions
        crefInfoList = collectParallelVariablesinExps(crefInfoList,{exp1},inInfo);

        // check the rest
        crefInfoList = collectParallelVariablesinExps(crefInfoList,restExps,inInfo);
      then crefInfoList;



    // ICONST, RCONST, SCONST, BCONST, ENUM_LITERAL
    //
    case(crefInfoList,_::restExps,_)
      then collectParallelVariablesinExps(crefInfoList,restExps,inInfo);

  end matchcontinue;
end collectParallelVariablesinExps;


protected function collectParallelVariablesInSubscriptList
  input list<tuple<DAE.ComponentRef,SourceInfo>> inCrefInfos;
  input list<DAE.Subscript> inSubscriptLst;
  input SourceInfo inInfo;
  output list<tuple<DAE.ComponentRef,SourceInfo>> outCrefInfos;

algorithm
  outCrefInfos := matchcontinue(inCrefInfos,inSubscriptLst,inInfo)
    local
      list<DAE.Subscript> restSubs;
      list<tuple<DAE.ComponentRef,SourceInfo>> crefInfoList;
      DAE.Exp exp1;


    case(_,{},_) then inCrefInfos;

    case(crefInfoList, DAE.INDEX(exp1)::restSubs,_)
      equation
        //check the sub exp.
        crefInfoList = collectParallelVariablesinExps(crefInfoList,{exp1},inInfo);

        //check the rest
        crefInfoList = collectParallelVariablesInSubscriptList(crefInfoList,restSubs,inInfo);
      then crefInfoList;

    case(crefInfoList,_::restSubs,_)
      then collectParallelVariablesInSubscriptList(crefInfoList,restSubs,inInfo);

  end matchcontinue;
end collectParallelVariablesInSubscriptList;

protected function checkValidNoRetcall
  input DAE.Exp exp;
  input SourceInfo info;
algorithm
  _ := match (exp,info)
    local
      String str;
    case (DAE.CALL(),_) then ();
    case (DAE.REDUCTION(),_) then ();
    case (DAE.TUPLE({}),_) then ();
    else
      equation
        str = ExpressionDump.printExpStr(exp);
        Error.addSourceMessage(Error.NORETCALL_INVALID_EXP,{str},info);
      then fail();
  end match;
end checkValidNoRetcall;

annotation(__OpenModelica_Interface="frontend");
end InstSection;
