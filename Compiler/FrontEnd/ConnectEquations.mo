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

encapsulated package ConnectEquations
" file:        ConnectEquations.mo
  package:     ConnectEquations
  description: Functions that generate connect equations.

"

public
import Absyn;
import Connect;
import DAE;
import ConnectionSets;

protected
import ConnectUtil;
import ComponentReference;
import Config;
import DAEUtil;
import Debug;
import ElementSource;
import Error;
import Expression;
import ExpressionSimplify;
import Flags;
import List;
import System;
import Types;

public
import Connect.Connections;
import Connect.Connection;
import Connect.Connector;
import Connect.ConnectorAttr;
import Connect.Face;
import DAE.ConnectorType;

protected
import ConnectionSets.DisjointSets;
import MetaModelica.Dangerous.listReverseInPlace;

public function generateEquations
  input list<list<Connector>> sets;
  output DAE.DAElist equations;
protected
  list<DAE.Element> set_eql, eql = {};
  Real flowThreshold = Flags.getConfigReal(Flags.FLOW_THRESHOLD);
algorithm
  for set in sets loop
    set_eql := match getSetType(set)
      case ConnectorType.POTENTIAL() then generatePotentialEquations(set);
      case ConnectorType.FLOW() then generateFlowEquations(set);
      case ConnectorType.STREAM() then generateStreamEquations(set, flowThreshold);
      case ConnectorType.NON_CONNECTOR()
        algorithm
          Error.addMessage(Error.INTERNAL_ERROR,
            {"ConnectEquations.generateEquations failed because of unknown connector type."});
        then
          fail();
    end match;

    eql := listAppend(set_eql, eql);
  end for;

  equations := DAE.DAE(eql);
end generateEquations;

protected function getSetType
  input list<Connector> set;
  output ConnectorType ty;
algorithm
  // All connectors in a set should have the same type, so pick the first.
  Connector.CONNECTOR(cty = ty) :: _ := set;
end getSetType;

protected function generatePotentialEquations
  "A non-flow connection set contains a number of components. Generating the
   equations from this set means equating all the components. For n components,
   this will give n-1 equations. For example, if the set contains the components
   X, Y.A and Z.B, the equations generated will be X = Y.A and X = Z.B. The
   order of the equations depends on whether the compiler flag orderConnections
   is true or false."
  input list<Connector> elements;
  output list<DAE.Element> equations = {};
protected
  partial function eqFunc
    input DAE.ComponentRef lhsCref;
    input DAE.ElementSource lhsSource;
    input DAE.ComponentRef rhsCref;
    input DAE.ElementSource rhsSource;
    output DAE.Element eq;
  end eqFunc;

  Connector c1;
  DAE.ComponentRef x, y;
  DAE.ElementSource source;
  Boolean is_const;
  eqFunc eqfunc;
algorithm
  if listEmpty(elements) then
    return;
  end if;

  c1 := listHead(elements);
  is_const := DAEUtil.isParamOrConstVarKind(c1.attr.variability);
  eqfunc := if is_const then makeEqualityAssert else makeEqualityEquation;

  if Config.orderConnections() then
    for c2 in listRest(elements) loop
      equations := eqfunc(c1.name, c1.source, c2.name, c2.source) :: equations;
    end for;
  else
    for c2 in listRest(elements) loop
      (x, y) := Util.swap(shouldFlipEquEquation(c1.name, c1.source), c1.name, c2.name);
      equations := eqfunc(c1.name, c1.source, c2.name, c2.source) :: equations;
      c1 := c2;
    end for;
  end if;
end generatePotentialEquations;

protected function makeEqualityEquation
  input DAE.ComponentRef lhsCref;
  input DAE.ElementSource lhsSource;
  input DAE.ComponentRef rhsCref;
  input DAE.ElementSource rhsSource;
  output DAE.Element equalityEq;
protected
  DAE.ElementSource source;
algorithm
  source := ElementSource.mergeSources(lhsSource, rhsSource);
  source := ElementSource.addElementSourceConnect(source, (lhsCref, rhsCref));
  equalityEq := DAE.EQUEQUATION(lhsCref, rhsCref, source);
end makeEqualityEquation;

protected function makeEqualityAssert
  input DAE.ComponentRef lhsCref;
  input DAE.ElementSource lhsSource;
  input DAE.ComponentRef rhsCref;
  input DAE.ElementSource rhsSource;
  output DAE.Element equalityAssert;
protected
  DAE.ElementSource source;
  DAE.Exp lhs_exp, rhs_exp, rel_exp;
algorithm
  source := ElementSource.mergeSources(lhsSource, rhsSource);
  source := ElementSource.addElementSourceConnect(source, (lhsCref, rhsCref));
  lhs_exp := Expression.crefExp(lhsCref);
  rhs_exp := Expression.crefExp(rhsCref);
  rel_exp := DAE.RELATION(lhs_exp, DAE.EQUAL(DAE.T_BOOL_DEFAULT), rhs_exp, -1, NONE());
  equalityAssert := DAE.ASSERT(rel_exp, DAE.SCONST("automatically generated from connect"),
    DAE.ASSERTIONLEVEL_ERROR, source);
end makeEqualityAssert;

protected function shouldFlipEquEquation
  "If the flag +orderConnections=false is used, then we should keep the order of
   the connector elements as they occur in the connection (if possible). In that
   case we check if the cref of the first argument to the first connection
   stored in the element source is a prefix of the connector element cref. If
   it isn't, indicate that we should flip the generated equation."
  input DAE.ComponentRef lhsCref;
  input DAE.ElementSource lhsSource;
  output Boolean shouldFlip;
algorithm
  shouldFlip := match lhsSource
    local
      DAE.ComponentRef lhs;

    case DAE.SOURCE(connectEquationOptLst = (lhs, _) :: _)
      then not ComponentReference.crefPrefixOf(lhs, lhsCref);

    else false;
  end match;
end shouldFlipEquEquation;

protected function generateFlowEquations
  "Generating equations from a flow connection set is a little trickier that
   from a non-flow set. Only one equation is generated, but it has to consider
   whether the components were inside or outside connectors. This function
   creates a sum expression of all components (some of which will be negated),
   and then returns the equation where this sum is equal to 0.0."
  input list<Connector> elements;
  output list<DAE.Element> equations;
protected
  Connector c = listHead(elements);
  DAE.ElementSource src = c.source;
  DAE.Exp sum;
algorithm
  sum := makeFlowExp(c);

  for e in listRest(elements) loop
    sum := Expression.makeRealAdd(sum, makeFlowExp(e));
    src := ElementSource.mergeSources(src, e.source);
  end for;

  equations := {DAE.EQUATION(sum, DAE.RCONST(0.0), src)};
end generateFlowEquations;

protected function makeFlowExp
  "Creates an expression from a connector element, which is the element itself
   if it's an inside connector, or negated if it's outside."
  input Connector element;
  output DAE.Exp exp;
algorithm
  exp := Expression.crefExp(element.name);

  if isOutsideElement(element) then
    exp := Expression.negateReal(exp);
  end if;
end makeFlowExp;

protected function generateStreamEquations
  "Generates the equations for a stream connection set."
  input list<Connector> elements;
  input Real flowThreshold;
  output list<DAE.Element> equations;
algorithm
  equations := match elements
    local
      DAE.ComponentRef cr1, cr2;
      DAE.ElementSource src, src1, src2;
      DAE.Exp cref1, cref2, e1, e2;
      list<Connector> inside, outside;

    // Unconnected stream connector, do nothing!
    case ({Connector.CONNECTOR(face = Face.INSIDE())})
      then {};

    // Both inside, do nothing!
    case ({Connector.CONNECTOR(face = Face.INSIDE()),
           Connector.CONNECTOR(face = Face.INSIDE())})
      then {};

    // Both outside:
    // cr1 = inStream(cr2);
    // cr2 = inStream(cr1);
    case ({Connector.CONNECTOR(name = cr1, face = Face.OUTSIDE(), source = src1),
           Connector.CONNECTOR(name = cr2, face = Face.OUTSIDE(), source = src2)})
      algorithm
        cref1 := Expression.crefExp(cr1);
        cref2 := Expression.crefExp(cr2);
        e1 := makeInStreamCall(cref2);
        e2 := makeInStreamCall(cref1);
        src := ElementSource.mergeSources(src1, src2);
      then
        {DAE.EQUATION(cref1, e1, src), DAE.EQUATION(cref2, e2, src)};

    // One inside, one outside:
    // cr1 = cr2;
    case ({Connector.CONNECTOR(name = cr1, source = src1),
           Connector.CONNECTOR(name = cr2, source = src2)})
      algorithm
        e1 := Expression.crefExp(cr1);
        e2 := Expression.crefExp(cr2);
        src := ElementSource.mergeSources(src1, src2);
      then
        {DAE.EQUATION(e1, e2, src)};

    // The general case with N inside connectors and M outside:
    else
      algorithm
        (outside, inside) := List.splitOnTrue(elements, isOutsideElement);
      then
        streamEquationGeneral(outside, inside, flowThreshold);

  end match;
end generateStreamEquations;

protected function isOutsideElement
  "Returns true if the connector element belongs to an outside connector."
  input Connector element;
  output Boolean isOutside;
algorithm
  isOutside := match element
    case Connector.CONNECTOR(face = Face.OUTSIDE()) then true;
    else false;
  end match;
end isOutsideElement;

protected function isZeroFlowMinMax
  "Returns true if the given flow attribute of a connector is zero."
  input DAE.ComponentRef streamCref;
  input Connector element;
  output Boolean isZero;
algorithm
  if compareCrefStreamSet(streamCref, element) then
    isZero := false;
  elseif isOutsideElement(element) then
    isZero := isZeroFlow(element, "max");
  else
    isZero := isZeroFlow(element, "min");
  end if;
end isZeroFlowMinMax;

protected function isZeroFlow
  "Returns true if the given flow attribute of a connector is zero."
  input Connector element;
  input String attr;
  output Boolean isZero;
protected
  DAE.Type ty;
  Option<DAE.Exp> attr_oexp;
  DAE.Exp flow_exp, attr_exp;
algorithm
  flow_exp := flowExp(element);
  ty := Expression.typeof(flow_exp);
  attr_oexp := Types.lookupAttributeExp(Types.getAttributes(ty), attr);
  if isSome(attr_oexp) then
    SOME(attr_exp) := attr_oexp;
    isZero := Expression.isZero(attr_exp);
  else
    isZero := false;
  end if;
end isZeroFlow;

protected function streamEquationGeneral
  "Generates an equation for an outside stream connector element."
  input list<Connector> outsideElements;
  input list<Connector> insideElements;
  input Real flowThreshold;
  output list<DAE.Element> equations = {};
protected
  list<Connector> outside;
  DAE.Exp cref_exp, res;
  DAE.ElementSource src;
algorithm
  for e in outsideElements loop
    cref_exp := Expression.crefExp(e.name);
    outside := removeStreamSetElement(e.name, outsideElements);
    res := streamSumEquationExp(outside, insideElements, flowThreshold);
    // TODO: Handle element sources.
    src := ElementSource.addAdditionalComment(e.source, " equation generated by stream handling");
    equations := DAE.EQUATION(cref_exp, res, src) :: equations;
  end for;
end streamEquationGeneral;

protected function streamSumEquationExp
  "Generates the sum expression used by stream connector equations, given M
  outside connectors and N inside connectors:

    (sum(max(-flow_exp[i], eps) * stream_exp[i] for i in N) +
     sum(max( flow_exp[i], eps) * inStream(stream_exp[i]) for i in M)) /
    (sum(max(-flow_exp[i], eps) for i in N) +
     sum(max( flow_exp[i], eps) for i in M))

  where eps = inFlowThreshold.
  "
  input list<Connector> outsideElements;
  input list<Connector> insideElements;
  input Real flowThreshold;
  output DAE.Exp sumExp;
protected
  DAE.Exp outside_sum1, outside_sum2, inside_sum1, inside_sum2, res;
algorithm
  if listEmpty(outsideElements) then
    // No outside components.
    inside_sum1 := sumMap(insideElements, sumInside1, flowThreshold);
    inside_sum2 := sumMap(insideElements, sumInside2, flowThreshold);
    sumExp := Expression.expDiv(inside_sum1, inside_sum2);
  elseif listEmpty(insideElements) then
    // No inside components.
    outside_sum1 := sumMap(outsideElements, sumOutside1, flowThreshold);
    outside_sum2 := sumMap(outsideElements, sumOutside2, flowThreshold);
    sumExp := Expression.expDiv(outside_sum1, outside_sum2);
  else
    // Both outside and inside components.
    outside_sum1 := sumMap(outsideElements, sumOutside1, flowThreshold);
    outside_sum2 := sumMap(outsideElements, sumOutside2, flowThreshold);
    inside_sum1 := sumMap(insideElements, sumInside1, flowThreshold);
    inside_sum2 := sumMap(insideElements, sumInside2, flowThreshold);
    sumExp := Expression.expDiv(Expression.expAdd(outside_sum1, inside_sum1),
                                   Expression.expAdd(outside_sum2, inside_sum2));
  end if;
end streamSumEquationExp;

protected function sumMap
  "Creates a sum expression by applying the given function on the list of
  elements and summing up the resulting expressions."
  input list<Connector> elements;
  input FuncType func;
  input Real flowThreshold;
  output DAE.Exp exp;

  partial function FuncType
    input Connector element;
    input Real flowThreshold;
    output DAE.Exp exp;
  end FuncType;
algorithm
  exp := Expression.expAdd(func(e, flowThreshold) for e in listReverse(elements));
end sumMap;

protected function streamFlowExp
  "Returns the stream and flow component in a stream set element as expressions."
  input Connector element;
  output DAE.Exp streamExp;
  output DAE.Exp flowExp;
protected
  DAE.ComponentRef flow_cr;
algorithm
  Connector.CONNECTOR(cty = ConnectorType.STREAM(SOME(flow_cr))) := element;
  streamExp := Expression.crefExp(element.name);
  flowExp := Expression.crefExp(flow_cr);
end streamFlowExp;

protected function flowExp
  "Returns the flow component in a stream set element as an expression."
  input Connector element;
  output DAE.Exp flowExp;
protected
  DAE.ComponentRef flow_cr;
algorithm
  Connector.CONNECTOR(cty = ConnectorType.STREAM(SOME(flow_cr))) := element;
  flowExp := Expression.crefExp(flow_cr);
end flowExp;

protected function sumOutside1
  "Helper function to streamSumEquationExp. Returns the expression
    max(flow_exp, eps) * inStream(stream_exp)
  given a stream set element."
  input Connector element;
  input Real flowThreshold;
  output DAE.Exp exp;
protected
  DAE.Exp stream_exp, flow_exp, flow_threshold;
algorithm
  (stream_exp, flow_exp) := streamFlowExp(element);
  flow_threshold := DAE.RCONST(flowThreshold);
  exp := Expression.expMul(makePositiveMaxCall(flow_exp, flow_threshold),
                              makeInStreamCall(stream_exp));
end sumOutside1;

protected function sumInside1
  "Helper function to streamSumEquationExp. Returns the expression
    max(-flow_exp, eps) * stream_exp
  given a stream set element."
  input Connector element;
  input Real flowThreshold;
  output DAE.Exp exp;
protected
  DAE.Exp stream_exp, flow_exp, flow_threshold;
  DAE.Type flowTy, streamTy;
algorithm
  (stream_exp, flow_exp) := streamFlowExp(element);
  flowTy := Expression.typeof(flow_exp);
  flow_exp := DAE.UNARY(DAE.UMINUS(flowTy), flow_exp);
  flow_threshold := DAE.RCONST(flowThreshold);
  exp := Expression.expMul(makePositiveMaxCall(flow_exp, flow_threshold), stream_exp);
end sumInside1;

protected function sumOutside2
  "Helper function to streamSumEquationExp. Returns the expression
    max(flow_exp, eps)
  given a stream set element."
  input Connector element;
  input Real flowThreshold;
  output DAE.Exp exp;
protected
  DAE.Exp flow_exp;
algorithm
  flow_exp := flowExp(element);
  exp := makePositiveMaxCall(flow_exp, DAE.RCONST(flowThreshold));
end sumOutside2;

protected function sumInside2
  "Helper function to streamSumEquationExp. Returns the expression
    max(-flow_exp, eps)
  given a stream set element."
  input Connector element;
  input Real flowThreshold;
  output DAE.Exp exp;
protected
  DAE.Exp flow_exp;
  DAE.Type flowTy;
algorithm
  flow_exp := flowExp(element);
  flowTy := Expression.typeof(flow_exp);
  flow_exp := DAE.UNARY(DAE.UMINUS(flowTy), flow_exp);
  exp := makePositiveMaxCall(flow_exp, DAE.RCONST(flowThreshold));
end sumInside2;

protected function makeInStreamCall
  "Creates an inStream call expression."
  input DAE.Exp streamExp;
  output DAE.Exp inStreamCall;
  annotation(__OpenModelica_EarlyInline = true);
protected
  DAE.Type ty;
algorithm
  ty := Expression.typeof(streamExp);
  inStreamCall := Expression.makeBuiltinCall("inStream", {streamExp}, ty, false);
end makeInStreamCall;

protected function makePositiveMaxCall
  "Generates a max(flow_exp, eps) call."
  input DAE.Exp flowExp;
  input DAE.Exp flowThreshold;
  output DAE.Exp positiveMaxCall;
  annotation(__OpenModelica_EarlyInline = true);
protected
  DAE.Type ty;
  list<DAE.Var> attr;
  Option<DAE.Exp> nominal_oexp;
  DAE.Exp nominal_exp, flow_threshold;
algorithm
  ty := Expression.typeof(flowExp);
  nominal_oexp := Types.lookupAttributeExp(Types.getAttributes(ty), "nominal");

  if isSome(nominal_oexp) then
    SOME(nominal_exp) := nominal_oexp;
    flow_threshold := Expression.expMul(flowThreshold, nominal_exp);
  else
    flow_threshold := flowThreshold;
  end if;

  positiveMaxCall :=
    DAE.CALL(Absyn.IDENT("max"), {flowExp, flow_threshold},
      DAE.CALL_ATTR(
        ty,
        false,
        true,
        false,
        false,
        DAE.NO_INLINE(),
        DAE.NO_TAIL()));
end makePositiveMaxCall;

protected function removeStreamSetElement
  "This function removes the given cref from a connection set."
  input DAE.ComponentRef cref;
  input output list<Connector> elements;
algorithm
  elements := List.deleteMemberOnTrue(cref, elements, compareCrefStreamSet);
end removeStreamSetElement;

protected function compareCrefStreamSet
  "Helper function to removeStreamSetElement. Checks if the cref in a stream set
  element matches the given cref."
  input DAE.ComponentRef cref;
  input Connector element;
  output Boolean matches;
algorithm
  matches := ComponentReference.crefEqualNoStringCompare(cref, element.name);
end compareCrefStreamSet;

//public function generateAssertion
//  input Connector inLhsConnector;
//  input Connector inRhsConnector;
//  input SourceInfo inInfo;
//  input list<Equation> inEquations;
//  output list<Equation> outEquations;
//  output Boolean outIsOnlyConst;
//algorithm
//  (outEquations, outIsOnlyConst) := matchcontinue(inLhsConnector, inRhsConnector,
//      inInfo, inEquations)
//    local
//      DAE.ComponentRef lhs, rhs;
//      DAE.Exp lhs_exp, rhs_exp;
//      list<Equation> eql;
//      Boolean is_only_const;
//      DAE.Type lhs_ty, rhs_ty, ty;
//
//    // Variable simple connection, nothing to do.
//    case (NFConnect2.CONNECTOR(), NFConnect2.CONNECTOR(), _, _)
//      equation
//        false = NFConnectUtil2.isConstOrComplexConnector(inLhsConnector);
//        false = NFConnectUtil2.isConstOrComplexConnector(inRhsConnector);
//      then
//        (inEquations, false);
//
//    // One or both of the connectors are constant/parameter or complex,
//    // generate assertion or error message.
//    case (NFConnect2.CONNECTOR(name = lhs, ty = lhs_ty),
//          NFConnect2.CONNECTOR(name = rhs, ty = rhs_ty), _, _)
//      equation
//        /* ------------------------------------------------------------------*/
//        // TODO: If we have mixed Real/Integer, one of these expression might
//        // need to be typecast. ty should be the common type.
//        /* ------------------------------------------------------------------*/
//        lhs_exp = DAE.CREF(lhs, lhs_ty);
//        rhs_exp = DAE.CREF(rhs, rhs_ty);
//        ty = lhs_ty;
//
//        (eql, is_only_const) = generateAssertion2(lhs_exp, rhs_exp,
//          ty, inInfo, inEquations);
//      then
//        (eql, is_only_const);
//
//  end matchcontinue;
//end generateAssertion;
//
//protected function generateAssertion2
//  input DAE.Exp inLhsExp;
//  input DAE.Exp inRhsExp;
//  input DAE.Type inType;
//  input SourceInfo inInfo;
//  input list<Equation> inEquations;
//  output list<Equation> outEquations;
//  output Boolean outIsOnlyConst;
//algorithm
//  (outEquations, outIsOnlyConst) :=
//  matchcontinue(inLhsExp, inRhsExp, inType, inInfo, inEquations)
//    local
//      DAE.Exp bin_exp, abs_exp, cond_exp;
//      Equation assertion;
//      list<DAE.Var> lhs_vars, lhs_rest, rhs_vars, rhs_rest;
//      DAE.ComponentRef lhs_cref, rhs_cref;
//      list<Equation> eql;
//      Boolean ioc;
//      String ty_str;
//
//    // One or both of the connectors are scalar Reals.
//    case (_, _, _, _, _)
//      equation
//        true = Types.isScalarReal(inType);
//        // Generate an 'abs(lhs - rhs) <= 0' assertion, to keep the flat Modelica
//        // somewhat similar to Modelica (which doesn't allow == for Reals).
//        bin_exp = DAE.BINARY(inLhsExp, DAE.SUB(inType), inRhsExp);
//        abs_exp = DAE.CALL(Absyn.IDENT("abs"), {bin_exp}, DAE.callAttrBuiltinReal);
//        cond_exp = DAE.RELATION(abs_exp, DAE.LESSEQ(inType), DAE.RCONST(0.0), 0, NONE());
//        assertion = makeAssertion(cond_exp, inInfo);
//      then
//        (assertion :: inEquations, true);
//
//    // Array connectors.
//    case (_, _, DAE.T_ARRAY(), _, _)
//      equation
//        /* ------------------------------------------------------------------*/
//        // TODO: Implement this.
//        /* ------------------------------------------------------------------*/
//        Error.addSourceMessage(Error.INTERNAL_ERROR,
//          {"Generating assertions for connections not yet implemented for arrays."},
//          inInfo);
//      then
//        fail();
//
//    // Complex connectors.
//    case (DAE.CREF(lhs_cref, DAE.T_COMPLEX(varLst = lhs_vars)),
//          DAE.CREF(rhs_cref, DAE.T_COMPLEX(varLst = rhs_vars)), _, _, _)
//      equation
//        (lhs_vars, lhs_rest) = List.splitOnTrue(lhs_vars, DAEUtil.isParamConstOrComplexVar);
//        (rhs_vars, rhs_rest) = List.splitOnTrue(rhs_vars, DAEUtil.isParamConstOrComplexVar);
//
//        ioc = listEmpty(lhs_rest) and listEmpty(rhs_rest);
//
//        (eql, ioc) = generateAssertion3(lhs_vars, rhs_vars,
//          lhs_cref, rhs_cref, inInfo, inEquations, ioc);
//      then
//        (eql, ioc);
//
//    // Other scalar types.
//    case (_, _, _, _, _)
//      equation
//        true = Types.isSimpleType(inType);
//        // Generate an 'lhs = rhs' assertion.
//        cond_exp = DAE.RELATION(inLhsExp, DAE.EQUAL(inType), inRhsExp, 0, NONE());
//        assertion = makeAssertion(cond_exp, inInfo);
//      then
//        (assertion :: inEquations, true);
//
//    else
//      equation
//        true = Flags.isSet(Flags.FAILTRACE);
//        Debug.trace("- ConnectUtil.generateConnectAssertion2 failed on unknown type ");
//        ty_str = Types.unparseType(inType);
//        Debug.traceln(ty_str);
//      then
//        fail();
//
//  end matchcontinue;
//end generateAssertion2;
//
//protected function makeAssertion
//  input DAE.Exp inCondition;
//  input SourceInfo inInfo;
//  output Equation outAssert;
//protected
//  DAE.Exp cond_exp, msg_exp;
//algorithm
//  /* ------------------------------------------------------------------*/
//  // TODO: Change this to a better message. Kept like this for now to be
//  // as close to the old instantiation as possible.
//  /* ------------------------------------------------------------------*/
//  msg_exp := DAE.SCONST("automatically generated from connect");
//  outAssert := NFInstTypes.ASSERT_EQUATION(inCondition, msg_exp,
//    DAE.ASSERTIONLEVEL_ERROR, inInfo);
//end makeAssertion;
//
//protected function generateAssertion3
//  input list<DAE.Var> inLhsVar;
//  input list<DAE.Var> inRhsVar;
//  input DAE.ComponentRef inLhsCref;
//  input DAE.ComponentRef inRhsCref;
//  input SourceInfo inInfo;
//  input list<Equation> inEquations;
//  input Boolean inIsOnlyConst;
//  output list<Equation> outEquations;
//  output Boolean outIsOnlyConst;
//algorithm
//  (outEquations, outIsOnlyConst) := match(inLhsVar, inRhsVar,
//      inLhsCref, inRhsCref, inInfo, inEquations, inIsOnlyConst)
//    local
//      DAE.Var lhs_var, rhs_var;
//      list<DAE.Var> lhs_rest, rhs_rest;
//      list<Equation> eql;
//      Boolean ioc;
//
//    case (lhs_var :: lhs_rest, rhs_var :: rhs_rest, _, _, _, eql, _)
//      equation
//        (eql, ioc) = generateAssertion4(lhs_var, rhs_var,
//          inLhsCref, inRhsCref, inInfo, eql);
//        ioc = ioc and inIsOnlyConst;
//        (eql, ioc) = generateAssertion3(lhs_rest, rhs_rest,
//          inLhsCref, inRhsCref, inInfo, eql, ioc);
//      then
//        (eql, ioc);
//
//    case ({}, {}, _ ,_, _, _, _) then (inEquations, inIsOnlyConst);
//
//  end match;
//end generateAssertion3;
//
//protected function generateAssertion4
//  input DAE.Var inLhsVar;
//  input DAE.Var inRhsVar;
//  input DAE.ComponentRef inLhsCref;
//  input DAE.ComponentRef inRhsCref;
//  input SourceInfo inInfo;
//  input list<Equation> inEquations;
//  output list<Equation> outEquations;
//  output Boolean outIsOnlyConst;
//protected
//  Connector lhs_conn, rhs_conn;
//algorithm
//  lhs_conn := NFConnectUtil2.varToConnector(inLhsVar, inLhsCref, NFConnect2.INSIDE());
//  rhs_conn := NFConnectUtil2.varToConnector(inRhsVar, inRhsCref, NFConnect2.INSIDE());
//  (outEquations, outIsOnlyConst) := generateAssertion(lhs_conn, rhs_conn,
//    inInfo, inEquations);
//end generateAssertion4;

public function evaluateConnectionOperators
  "Evaluates connection operators inStream, actualStream and cardinality in the
   given DAE."
  input DisjointSets sets;
  input array<list<Connector>> setsArray;
  input output list<DAE.Element> daeElements;
protected
  Real flow_threshold;
  Boolean has_cardinality = System.getUsesCardinality();
algorithm
  // Only do this phase if we have any connection operators.
  if System.getHasStreamConnectors() or has_cardinality then
    flow_threshold := Flags.getConfigReal(Flags.FLOW_THRESHOLD);
    daeElements := DAEUtil.traverseDAEElementList(daeElements,
      function evaluateConnectionOperators2(
        hasCardinality = has_cardinality,
        setsArray = setsArray,
        flowThreshold = flow_threshold), sets);
    daeElements := simplifyDAEElements(has_cardinality, daeElements);
  end if;
end evaluateConnectionOperators;

protected function evaluateConnectionOperators2
  "Helper function to evaluateConnectionOperators."
  input output DAE.Exp exp;
  input output DisjointSets sets;
  input array<list<Connector>> setsArray;
  input Boolean hasCardinality;
  input Real flowThreshold;
protected
  Boolean changed;
algorithm
  (exp, changed) := Expression.traverseExpBottomUp(exp,
    function evaluateConnectionOperatorsExp(
      sets = sets,
      setsArray = setsArray,
      flowThreshold = flowThreshold), false);

  // Only apply simplify if the expression changed *AND* we have cardinality.
  if changed and hasCardinality then
    exp := ExpressionSimplify.simplify(exp);
  end if;
end evaluateConnectionOperators2;

protected function evaluateConnectionOperatorsExp
  "Helper function to evaluateConnectionOperators2. Checks if the given
   expression is a call to inStream or actualStream, and if so calls the
   appropriate function in ConnectUtil to evaluate the call."
  input output DAE.Exp exp;
  input DisjointSets sets;
  input array<list<Connector>> setsArray;
  input Real flowThreshold;
  input output Boolean changed;
algorithm
  (exp, changed) := match exp
    local
      DAE.ComponentRef cr;
      DAE.Exp e;

    case DAE.CALL(path = Absyn.IDENT("inStream"),
                  expLst = {DAE.CREF(componentRef = cr)})
      algorithm
        e := evaluateInStream(cr, sets, setsArray, flowThreshold);
      then
        (e, true);

    case DAE.CALL(path = Absyn.IDENT("actualStream"),
                  expLst = {DAE.CREF(componentRef = cr)})
      algorithm
        e := evaluateActualStream(cr, sets, setsArray, flowThreshold);
      then
        (e, true);

    case DAE.CALL(path = Absyn.IDENT("cardinality"),
                  expLst = {DAE.CREF(componentRef = cr)})
      algorithm
        e := evaluateCardinality(cr, sets);
      then
        (e, true);

    else (exp, changed);

  end match;
end evaluateConnectionOperatorsExp;

protected function evaluateInStream
  "This function evaluates the inStream operator for a component reference,
   given the connection sets."
  input DAE.ComponentRef streamCref;
  input DisjointSets sets;
  input array<list<Connector>> setsArray;
  input Real flowThreshold;
  output DAE.Exp exp;
protected
  Connector e;
  list<Connector> sl;
  Integer set;
algorithm
  e := ConnectUtil.makeConnector(streamCref, DAE.T_UNKNOWN_DEFAULT, Face.INSIDE(),
    ConnectorType.STREAM(NONE()), Connect.DEFAULT_ATTR, DAE.emptyElementSource);

  try
    set := ConnectionSets.findSetArrayIndex(e, sets);
    sl := arrayGet(setsArray, set);
  else
    sl := {e};
  end try;

  print("inStream(" + ComponentReference.printComponentRefStr(streamCref) + ")
  = {" + stringDelimitList(list(ConnectUtil.connectorStr(c) for c in sl), ", ") + "}\n");
  exp := generateInStreamExp(streamCref, sl, sets, setsArray, flowThreshold);
end evaluateInStream;

protected function generateInStreamExp
  "Helper function to evaluateInStream. Generates an expression for inStream
  given a connection set."
  input DAE.ComponentRef streamCref;
  input list<Connector> streams;
  input DisjointSets sets;
  input array<list<Connector>> setsArray;
  input Real flowThreshold;
  output DAE.Exp exp;
protected
  list<Connector> reducedStreams;
algorithm
  print("1\n");
  reducedStreams := List.filterOnFalse(streams, function isZeroFlowMinMax(streamCref = streamCref));
  print("2\n");

  exp := match reducedStreams
    local
      DAE.ComponentRef c;
      Face f1, f2;
      DAE.Exp e;
      list<Connector>  inside, outside;

    // Unconnected stream connector:
    // inStream(c) = c;
    case {Connector.CONNECTOR(name = c, face = Face.INSIDE())}
      then Expression.crefExp(c);

    // Two inside connected stream connectors:
    // inStream(c1) = c2;
    // inStream(c2) = c1;
    case {Connector.CONNECTOR(face = Face.INSIDE()),
          Connector.CONNECTOR(face = Face.INSIDE())}
      algorithm
        {Connector.CONNECTOR(name = c)} :=
          removeStreamSetElement(streamCref, reducedStreams);
        e := Expression.crefExp(c);
      then
        e;

    // One inside, one outside connected stream connector:
    // inStream(c1) = inStream(c2);
    case {Connector.CONNECTOR(face = f1),
        Connector.CONNECTOR(face = f2)} guard not ConnectUtil.faceEqual(f1, f2)
      algorithm
        {Connector.CONNECTOR(name = c)} :=
          removeStreamSetElement(streamCref, reducedStreams);
        e := evaluateInStream(c, sets, setsArray, flowThreshold);
      then
        e;

    // The general case:
    else
      algorithm
        (outside, inside) := List.splitOnTrue(reducedStreams, isOutsideElement);
        inside := removeStreamSetElement(streamCref, inside);
        e := streamSumEquationExp(outside, inside, flowThreshold);
        // Evaluate any inStream calls that were generated.
        e := evaluateConnectionOperators2(e, sets, setsArray, false, flowThreshold);
      then
        e;
  end match;
end generateInStreamExp;

protected function evaluateActualStream
  "This function evaluates the actualStream operator for a component reference,
  given the connection sets."
  input DAE.ComponentRef streamCref;
  input DisjointSets sets;
  input array<list<Connector>> setsArray;
  input Real flowThreshold;
  output DAE.Exp exp;
protected
  DAE.ComponentRef flow_cr;
  DAE.Exp e, flow_exp, stream_exp, instream_exp, rel_exp;
  DAE.Type ety;
  Integer flow_dir;
algorithm
  //flow_cr := getStreamFlowAssociation(streamCref, sets);
  //ety := ComponentReference.crefLastType(flow_cr);
  //flow_dir := evaluateFlowDirection(ety);

  //// Select a branch if we know the flow direction, otherwise generate the whole
  //// if-equation.
  //if flow_dir == 1 then
  //  rel_exp := evaluateInStream(streamCref, sets, setsArray, flowThreshold);
  //elseif flow_dir == -1 then
  //  rel_exp := Expression.crefExp(streamCref);
  //else
  //  flow_exp := Expression.crefExp(flow_cr);
  //  stream_exp := Expression.crefExp(streamCref);
  //  instream_exp := evaluateInStream(streamCref, sets, setsArray, flowThreshold);
  //  rel_exp := DAE.IFEXP(
  //    DAE.RELATION(flow_exp, DAE.GREATER(ety), DAE.RCONST(0.0), -1, NONE()),
  //    instream_exp, stream_exp);
  //end if;

  //// actualStream(stream_var) = smooth(0, if flow_var > 0 then inStream(stream_var)
  ////                                                      else stream_var);
  //exp := DAE.CALL(Absyn.IDENT("smooth"), {DAE.ICONST(0), rel_exp},
  //  DAE.callAttrBuiltinReal);

  exp := DAE.ICONST(0);
end evaluateActualStream;

protected function evaluateFlowDirection
  "Checks the min/max attributes of a flow variables type to try and determine
   the flow direction. If the flow is positive 1 is returned, if it is negative
   -1, otherwise 0 if the direction can't be decided."
  input DAE.Type ty;
  output Integer direction = 0;
protected
  list<DAE.Var> attr;
  Option<Values.Value> min_oval, max_oval;
  Real min_val, max_val;
algorithm
  attr := Types.getAttributes(ty);
  if listEmpty(attr) then return; end if;

  min_oval := Types.lookupAttributeValue(attr, "min");
  max_oval := Types.lookupAttributeValue(attr, "max");

  direction := match (min_oval, max_oval)
    // No attributes, flow direction can't be decided.
    case (NONE(), NONE()) then 0;
    // Flow is positive if min is positive.
    case (SOME(Values.REAL(min_val)), NONE())
      then if min_val >= 0 then 1 else 0;
    // Flow is negative if max is negative.
    case (NONE(), SOME(Values.REAL(max_val)))
      then if max_val <= 0 then -1 else 0;
    // Flow is positive if both min and max are positive, negative if they are
    // both negative, otherwise undecideable.
    case (SOME(Values.REAL(min_val)), SOME(Values.REAL(max_val)))
      then
        if min_val >= 0 and max_val >= min_val then 1
        elseif max_val <= 0 and min_val <= max_val then -1
        else 0;
    else 0;
  end match;
end evaluateFlowDirection;

protected function evaluateCardinality
  input DAE.ComponentRef cref;
  input DisjointSets sets;
  output DAE.Exp exp;
algorithm
  //exp := DAE.ICONST(getConnectCount(cref, sets.sets));
  exp := DAE.ICONST(0);
end evaluateCardinality;

protected function simplifyDAEElements
"run this only if we have cardinality"
  input Boolean hasCardinality;
  input output list<DAE.Element> daeElements;
protected
  list<DAE.Element> accum = {};
algorithm
  if not hasCardinality then
    return;
  end if;

  for e in daeElements loop
    accum := matchcontinue e
      case DAE.IF_EQUATION()
        then listAppend(simplifyDAEIfEquation(e.condition1, e.equations2, e.equations3), accum);
      case DAE.INITIAL_IF_EQUATION()
        then listAppend(simplifyDAEIfEquation(e.condition1, e.equations2, e.equations3), accum);
      case DAE.ASSERT(condition = DAE.BCONST(true)) then accum;
      else e :: accum;
    end matchcontinue;
  end for;

  daeElements := listReverse(accum);
end simplifyDAEElements;

protected function simplifyDAEIfEquation
  input list<DAE.Exp> conditions;
  input list<list<DAE.Element>> branches;
  input list<DAE.Element> elseBranch;
  output list<DAE.Element> elements;
protected
  Boolean cond_value;
  list<list<DAE.Element>> rest_branches = branches;
algorithm
  for cond in conditions loop
    DAE.BCONST(cond_value) := cond;

    // Condition is true, substitute the if-equation with the branch contents.
    if cond_value == true then
      elements := listReverse(listHead(rest_branches));
      return;
    end if;

    // Condition is false, discard the branch and continue with the other branches.
    rest_branches := listRest(rest_branches);
  end for;

  // All conditions were false, substitute if-equation with else-branch contents.
  elements := listReverse(elseBranch);
end simplifyDAEIfEquation;

annotation(__OpenModelica_Interface="frontend");
end ConnectEquations;
