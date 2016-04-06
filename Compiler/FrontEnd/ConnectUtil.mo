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

encapsulated package ConnectUtil
" file:        ConnectUtil.mo
  package:     ConnectUtil
  description: Connection set management
"

// public imports
public
import Absyn;
import SCode;
import ClassInf;
import Config;
import Connect;
import DAE;
import FCore;
import InnerOuter;
import Prefix;
import ConnectionGraph;
import NFInstUtil;

// protected imports
protected
import ComponentReference;
import ConnectEquations;
import DAEUtil;
import Debug;
import ElementSource;
import Error;
import Expression;
import ExpressionDump;
import ExpressionSimplify;
import Flags;
import List;
import Lookup;
import PrefixUtil;
import System;
import Types;
import Util;

// Import some types from Connect.
import Connect.Face;
import Connect.Connector;
import Connect.ConnectorAttr;
import Connect.Connection;
import Connect.Connections;
import ConnectionSets.DisjointSets;
import DAE.ConnectorType;

import MetaModelica.Dangerous.listReverseInPlace;

public function resolveConnections
  input output DAE.DAElist dae;
protected
  list<DAE.Element> elements;
  Connections connections;
  list<Connector> flow_vars;
  DAE.DAElist conn_dae;
  DisjointSets sets;
  array<list<Connector>> sets_array;
algorithm
  //System.startTimer();
  (connections, flow_vars, elements) := collectConnections(dae.elementLst);
  sets := ConnectionSets.fromConnections(connections.connections, listReverse(flow_vars));
  (sets_array, sets) := ConnectionSets.extractSets(sets);
  conn_dae := ConnectEquations.generateEquations(arrayList(sets_array));
  elements := ConnectEquations.evaluateConnectionOperators(sets, sets_array, elements);
  // TODO: Remove listReverse.
  dae := DAE.DAE(List.append_reverse(elements, listReverse(conn_dae.elementLst)));
  //System.stopTimer();
  //print("resolveConnections: " + String(System.getTimerIntervalTime()) + "\n");
end resolveConnections;

protected function collectConnections
  input list<DAE.Element> elements;
  output Connections connections;
  output list<Connector> flowVariables = {};
  output list<DAE.Element> otherElements = {};
protected
  Connector c1, c2;
  list<Connection> connl = {};
algorithm
  for e in elements loop
    _ := match e
      case DAE.VAR(connectorType = DAE.FLOW())
        algorithm
          c1 := Connector.CONNECTOR(e.componentRef, e.ty, Face.INSIDE(), e.connectorType,
            ConnectorAttr.CONN_ATTR(e.kind, e.protection, e.direction), e.source);
          flowVariables := c1 :: flowVariables;
          otherElements := e :: otherElements;
        then
          ();

      case DAE.CONNECT_EQUATION()
        algorithm
          c1 := daeElementToConnector(e.lhsElement, e.lhsFace);
          c2 := daeElementToConnector(e.rhsElement, e.rhsFace);
          connl := Connection.CONNECTION(c1, c2, e.source.info) :: connl;
        then
          ();

      else
        algorithm
          otherElements := e :: otherElements;
        then
          ();

    end match;
  end for;

  connl := listReverseInPlace(connl);
  connections := Connections.CONNECTIONS(connl, {}, {}, {});
end collectConnections;

protected function daeElementToConnector
  input DAE.Element variable;
  input Connect.Face face;
  output Connector conn;
protected
  DAE.Element v;
algorithm
  conn := match variable
    case v as DAE.VAR()
      then Connector.CONNECTOR(v.componentRef, v.ty, face, v.connectorType,
        ConnectorAttr.CONN_ATTR(v.kind, v.protection, v.direction), v.source);
  end match;
end daeElementToConnector;

public function makeConnector
  input DAE.ComponentRef name;
  input DAE.Type ty;
  input Connect.Face face;
  input ConnectorType connectorType;
  input ConnectorAttr connectorAttr;
  input DAE.ElementSource source;
  output Connector conn;
algorithm
  conn := Connector.CONNECTOR(name, ty, face, connectorType, connectorAttr, source);
end makeConnector;

protected function renameConnector
  input DAE.ComponentRef name;
  input output Connector conn;
algorithm
  conn.name := name;
end renameConnector;

public function connectorEqual
  input Connector connector1;
  input Connector connector2;
  output Boolean isEqual;
algorithm
  isEqual := faceEqual(connector1.face, connector2.face) and
    ComponentReference.crefEqualNoStringCompare(connector1.name, connector2.name);
end connectorEqual;

public function connectorTypeEqual
  input ConnectorType type1;
  input ConnectorType type2;
  output Boolean isEqual = valueConstructor(type1) == valueConstructor(type2);
end connectorTypeEqual;

public function isPotential
  input ConnectorType connectorType;
  output Boolean isPotential;
algorithm
  isPotential := match connectorType
    case ConnectorType.POTENTIAL() then true;
    else false;
  end match;
end isPotential;

public function translateSCodeConnectorType
  input SCode.ConnectorType scodeConnectorType;
  output ConnectorType connectorType;
algorithm
  connectorType := match scodeConnectorType
    case SCode.POTENTIAL() then ConnectorType.POTENTIAL();
    case SCode.FLOW() then ConnectorType.FLOW();
    case SCode.STREAM() then ConnectorType.STREAM(NONE());
  end match;
end translateSCodeConnectorType;

public function translateConnectorTypeToSCode
  input ConnectorType connectorType;
  output SCode.ConnectorType scodeConnectorType;
algorithm
  scodeConnectorType := match connectorType
    case ConnectorType.POTENTIAL() then SCode.POTENTIAL();
    case ConnectorType.FLOW() then SCode.FLOW();
    case ConnectorType.STREAM() then SCode.STREAM();
  end match;
end translateConnectorTypeToSCode;

public function isEmptyConnections
  input Connections connections;
  output Boolean isEmpty;
algorithm
  isEmpty := match connections
    case Connections.CONNECTIONS({}, {}, {}, {}) then true;
    else false;
  end match;
end isEmptyConnections;

public function isExpandable
  input DAE.ComponentRef name;
  output Boolean expandableConnector;
algorithm
  expandableConnector := false;
  //expandableConnector := match(name)
  //  case DAE.CREF_IDENT()
  //    then Types.isExpandableConnectorType(name.identType);

  //  case DAE.CREF_QUAL()
  //    then Types.isExpandableConnectorType(name.identType) or
  //         isExpandable(name.componentRef);
  //  else false;
  //end match;
end isExpandable;

public function connectionCount
  input Connections connections;
  output Integer count = listLength(connections.connections);
end connectionCount;

public function preExpandConnector
  input Connector conn;
  output list<Connector> connectors;
protected
  DAE.Type ty;
algorithm
  ty := Types.derivedBasicType(conn.ty);
  connectors := match ty
    case DAE.T_COMPLEX()
      then list(varToConnector(v, conn.name, conn.face, conn.source) for v in ty.varLst);

    // TODO: Expand complex arrays too? c[3] => {(c.x)[3], (c.y)[3]}
    else {conn};
  end match;
end preExpandConnector;

public function expandConnector
  input Connector conn;
  output list<Connector> connectors;
protected
  list<DAE.ComponentRef> crefs, prefixes = {};
  DAE.ComponentRef name;
  DAE.Type ty, conn_ty;
  Connector c;
algorithm
  name := conn.name;

  if not ComponentReference.crefIsIdent(name) then
    (prefixes, name) := expandConnectorPrefix(name);
  end if;

  ty := Types.derivedBasicType(conn.ty);
  connectors := match ty
    case DAE.T_ARRAY()
      algorithm
        crefs := ComponentReference.expandCref(name, false);
        c := conn;
        c.ty := Types.unliftArray(conn.ty);
      then // TODO: Remove listReverse
        listAppend(expandConnector(renameConnector(cr, c)) for cr in listReverse(crefs));

    case DAE.T_COMPLEX() // TODO: Remove listReverse
      then listAppend(expandConnector(varToConnector(v, name, conn.face, conn.source))
             for v in listReverse(ty.varLst));

    else {renameConnector(name, conn)};
  end match;

  if not listEmpty(prefixes) then
    connectors := List.productMap(prefixes, connectors, prefixConnector);
  end if;
end expandConnector;

protected function expandConnectorPrefix
  input DAE.ComponentRef cref;
  output list<DAE.ComponentRef> prefixes;
  output DAE.ComponentRef lastCref;
algorithm
  (prefixes, lastCref) := match cref
    local
      DAE.ComponentRef pre_cr;

    case DAE.CREF_IDENT() then ({}, cref);
    else
      algorithm
        (pre_cr, lastCref) := ComponentReference.splitCrefLast(cref);
        prefixes := ComponentReference.expandCref(pre_cr, false);
      then
        (prefixes, lastCref);

  end match;
end expandConnectorPrefix;

public function prefixConnector
  input DAE.ComponentRef prefix;
  input output Connector conn;
algorithm
  conn.name := ComponentReference.joinCrefs(prefix, conn.name);
end prefixConnector;

public function varToConnector
  input DAE.Var var;
  input DAE.ComponentRef prefixCref;
  input Face face;
  input DAE.ElementSource source;
  output Connector conn;
protected
  DAE.Ident name;
  DAE.Type ty;
  DAE.ComponentRef cref;
  SCode.ConnectorType scty;
  ConnectorType cty;
  SCode.Variability svar;
  DAE.VarKind kind;
  Absyn.Direction sdir;
  DAE.VarDirection dir;
  SCode.Visibility svis;
  DAE.VarVisibility vis;
  DAE.Attributes dattr;
  ConnectorAttr attr;
algorithm
  dattr := var.attributes;
  cref := ComponentReference.makeCrefIdent(var.name, var.ty, {});
  cref := ComponentReference.joinCrefs(prefixCref, cref);
  cty := translateSCodeConnectorType(dattr.connectorType);
  kind := NFInstUtil.translateVariability(dattr.variability);
  dir := NFInstUtil.translateDirection(dattr.direction);
  vis := NFInstUtil.translateVisibility(dattr.visibility);
  attr := ConnectorAttr.CONN_ATTR(kind, vis, dir);
  conn := makeConnector(cref, var.ty, face, cty, attr, source);
end varToConnector;

public function faceEqual "Test for face equality."
  input Face face1;
  input Face face2;
  output Boolean sameFaces = valueConstructor(face1) == valueConstructor(face2);
end faceEqual;

public function connectorFace
  "Determines whether a connector is inside or outside."
  input DAE.ComponentRef name;
  output Face face;
algorithm
  face := match name
    // Simple identifier => OUTSIDE
    case DAE.CREF_IDENT() then Face.OUTSIDE();

    // Qualified identifier => OUTSIDE if first identifier is connector, otherwise INSIDE.
    case DAE.CREF_QUAL()
      then if Types.isConnector(Types.arrayElementType(name.identType)) then
        Face.OUTSIDE() else Face.INSIDE();

  end match;
end connectorFace;

protected function checkConnectorBalance
  "Checks if a connector class is balanced or not, according to the rules in the
  Modelica 3.2 specification."
  input list<DAE.Var> vars;
  input Absyn.Path path;
  input SourceInfo info;
protected
  Integer potentials, flows, streams;
algorithm
  (potentials, flows, streams) := countConnectorVars(vars);
  true := checkConnectorBalance2(potentials, flows, streams, path, info);
  //print(Absyn.pathString(path) + " has:\n\t" +
  //  String(potentials) + " potential variables\n\t" +
  //  String(flows) + " flow variables\n\t" +
  //  String(streams) + " stream variables\n\n");
end checkConnectorBalance;

protected function checkConnectorBalance2
  input Integer potentialVars;
  input Integer flowVars;
  input Integer streamVars;
  input Absyn.Path path;
  input SourceInfo info;
  output Boolean isBalanced = true;
protected
  String error_str, flow_str, potential_str, class_str;
algorithm
  // Don't check connector balance for language version 2.x and earlier.
  if Config.languageStandardAtMost(Config.LanguageStandard.'2.x') then
    return;
  end if;

  // Modelica 3.2 section 9.3.1:
  // For each non-partial connector class the number of flow variables shall
  // be equal to the number of variables that are neither parameter, constant,
  // input, output, stream nor flow.
  if potentialVars <> flowVars then
    flow_str := String(flowVars);
    potential_str := String(potentialVars);
    class_str := Absyn.pathString(path);
    error_str := stringAppendList({
      "The number of potential variables (",
      potential_str,
      ") is not equal to the number of flow variables (",
      flow_str, ")."});
    Error.addSourceMessage(Error.UNBALANCED_CONNECTOR, {class_str, error_str}, info);

    // This should be a hard error, but there are models that contain such
    // connectors. So we print an error but return that the connector is balanced.
  end if;

  // Modelica 3.2 section 15.1:
  // A stream connector must have exactly one scalar variable with the flow prefix.
  if streamVars > 0 and flowVars <> 1 then
    flow_str := String(flowVars);
    class_str := Absyn.pathString(path);
    error_str := stringAppendList({
      "A stream connector must have exactly one flow variable, this connector has ",
      flow_str, " flow variables."});
    Error.addSourceMessage(Error.INVALID_STREAM_CONNECTOR,
      {class_str, error_str}, info);
    isBalanced := false;
  end if;
end checkConnectorBalance2;

protected function countConnectorVars
  "Given a list of connector variables, this function counts how many potential,
  flow and stream variables it contains."
  input list<DAE.Var> vars;
  output Integer potentialVars = 0;
  output Integer flowVars = 0;
  output Integer streamVars = 0;
protected
  DAE.Type ty, ty2;
  DAE.Attributes attr;
  Integer n, p, f, s;
algorithm
  for var in vars loop
    DAE.TYPES_VAR(ty = ty, attributes = attr) := var;
    ty2 := Types.arrayElementType(ty);

    // Check if we have a connector inside a connector.
    if Types.isConnector(ty2) then
      // If we have an array of connectors, count the elements.
      n := product(dim for dim in Types.getDimensionSizes(ty));
      // Count the number of different variables inside the connector, and then
      // multiply those numbers with the dimensions of the array.
      (p, f, s) := countConnectorVars(Types.getConnectorVars(ty2));

      // If the variable is input/output we don't count potential variables.
      if Absyn.isInputOrOutput(DAEUtil.getAttrDirection(attr)) then
        p := 0;
      end if;

      potentialVars := potentialVars + p * n;
      flowVars := flowVars + f * n;
      streamVars := streamVars + s * n;
    else
      _ := match attr
        // A flow variable.
        case DAE.ATTR(connectorType = DAE.FLOW())
          algorithm
            flowVars := flowVars + sizeOfType(var.ty);
          then
            ();

        // A stream variable.
        case DAE.ATTR(connectorType = DAE.STREAM())
          algorithm
            streamVars := streamVars + sizeOfType(var.ty);
          then
            ();

        // A potential variable.
        case DAE.ATTR(direction = Absyn.BIDIR(), variability = SCode.VAR())
          algorithm
            potentialVars := potentialVars + sizeOfType(var.ty);
          then
            ();

        else ();
      end match;
    end if;
  end for;
end countConnectorVars;

protected function sizeOfVariableList
  "Calls sizeOfVariable on a list of variables, and adds up the results."
  input list<DAE.Var> vars;
  output Integer size = 0;
algorithm
  for var in vars loop
    size := size + sizeOfType(var.ty);
  end for;
end sizeOfVariableList;

protected function sizeOfType
  "Different types of variables have different size, for example arrays. This
   function checks the size of one variable."
  input DAE.Type ty;
  output Integer size;
algorithm
  size := match ty
    local
      Integer n;
      DAE.Type t;
      list<DAE.Var> v;

    // Scalar values consist of one element.
    case DAE.T_INTEGER() then 1;
    case DAE.T_REAL() then 1;
    case DAE.T_STRING() then 1;
    case DAE.T_BOOL() then 1;
    case DAE.T_ENUMERATION(index = NONE()) then 1;
    // The size of an array is its dimension multiplied with the size of its type.
    case DAE.T_ARRAY()
      then intMul(Expression.dimensionSize(dim) for dim in ty.dims) * sizeOfType(ty.ty);
    // The size of a complex type without an equalityConstraint (such as a
    // record), is the sum of the sizes of its components.
    case DAE.T_COMPLEX(varLst = v, equalityConstraint = NONE())
      then sizeOfVariableList(v);
    // The size of a complex type with an equalityConstraint function is
    // determined by the size of the return value of that function.
    case DAE.T_COMPLEX(equalityConstraint = SOME((_, n, _))) then n;
    // The size of a basic subtype with equality constraint is ZERO.
    case DAE.T_SUBTYPE_BASIC(equalityConstraint = SOME(_)) then 0;
    // The size of a basic subtype is the size of the extended type.
    case DAE.T_SUBTYPE_BASIC(complexType = t) then sizeOfType(t);
    // Anything we forgot?
    else
      algorithm
        true := Flags.isSet(Flags.FAILTRACE);
        Debug.traceln("- ConnectUtil.sizeOfType failed on " + Types.printTypeStr(ty));
      then
        fail();
  end match;
end sizeOfType;

public function checkShortConnectorDef
  "Checks a short connector definition that has extended a basic type, i.e.
   connector C = Real;."
  input ClassInf.State state;
  input SCode.Attributes attributes;
  input SourceInfo info;
  output Boolean isValid;
algorithm
  isValid := match(state, attributes)
    local
      Integer pv = 0, fv = 0, sv = 0;
      SCode.ConnectorType ct;

    // Extended from bidirectional basic type, which means that it can't be
    // balanced.
    case (ClassInf.CONNECTOR(),
        SCode.ATTR(connectorType = ct, direction = Absyn.BIDIR()))
      algorithm
        // The connector might be either flow, stream or neither.
        // This will set either fv, sv, or pv to 1, and the rest to 0, and
        // checkConnectorBalance2 will then be called to provide the appropriate
        // error message (or might actually succeed if +std=2.x or 1.x).
        if SCode.flowBool(ct) then
          fv := 1;
        elseif SCode.streamBool(ct) then
          sv := 1;
        else
          pv := 1;
        end if;
      then
        checkConnectorBalance2(pv, fv, sv, state.path, info);

    // All other cases are ok.
    else true;
  end match;
end checkShortConnectorDef;

public function checkConnectTypes
  input Connector lhs;
  input Connector rhs;
  input SourceInfo info;
algorithm
  ComponentReference.checkCrefSubscriptsBounds(lhs.name, info);
  ComponentReference.checkCrefSubscriptsBounds(rhs.name, info);

  if not Types.equivtypesOrRecordSubtypeOf(lhs.ty, rhs.ty) then
    printConnectTypeError(lhs, rhs, info);
  end if;

  if not connectorTypeEqual(lhs.cty, rhs.cty) then
    printConnectFlowStreamError(lhs, rhs, info);
  end if;

  if isSignalSource(lhs) and isSignalSource(rhs) then
    printConnectDirectionError(lhs, rhs, info);
  end if;
end checkConnectTypes;

protected function printConnectTypeError
  input Connector lhs;
  input Connector rhs;
  input SourceInfo info;
protected
  String cs1, cs2, lhs_str, rhs_str, str1, str2;
  list<DAE.Dimension> dims1, dims2;
algorithm
  lhs_str := ComponentReference.printComponentRefStr(lhs.name);
  rhs_str := ComponentReference.printComponentRefStr(rhs.name);

  // Give an error if the types are not identical.
  if not Types.equivtypesOrRecordSubtypeOf(Types.arrayElementType(lhs.ty),
      Types.arrayElementType(rhs.ty)) then
    (_, cs1) := Types.printConnectorTypeStr(lhs.ty);
    (_, cs2) := Types.printConnectorTypeStr(rhs.ty);
    Error.addSourceMessage(Error.CONNECT_INCOMPATIBLE_TYPES,
      {lhs_str, rhs_str, lhs_str, cs1, rhs_str, cs2}, info);
  end if;

  dims1 := Types.getDimensions(lhs.ty);
  dims2 := Types.getDimensions(rhs.ty);

  // Give an error if the dimensions are not identical.
  if not List.isEqualOnTrue(dims1, dims2, Expression.dimensionsEqual) then
    str1 := "[" + ExpressionDump.dimensionsString(dims1) + "]";
    str2 := "[" + ExpressionDump.dimensionsString(dims2) + "]";
    Error.addSourceMessage(Error.CONNECTOR_ARRAY_DIFFERENT,
      {lhs_str, rhs_str, str1, str2}, info);
  end if;

  fail();
end printConnectTypeError;

protected function printConnectFlowStreamError
  input Connector lhs;
  input Connector rhs;
  input SourceInfo info;
protected
  String lhs_str, rhs_str, pre_str1, pre_str2;
  list<String> err_strl;
algorithm
  lhs_str := ComponentReference.printComponentRefStr(lhs.name);
  rhs_str := ComponentReference.printComponentRefStr(rhs.name);
  pre_str1 := unparseConnectorType(lhs.cty);
  pre_str2 := unparseConnectorType(rhs.cty);
  err_strl := if isPotential(lhs.cty)
    then {pre_str2, rhs_str, lhs_str}
    else {pre_str1, lhs_str, rhs_str};
  Error.addSourceMessageAndFail(Error.CONNECT_PREFIX_MISMATCH, err_strl, info);
end printConnectFlowStreamError;

protected function printConnectDirectionError
  input Connector lhs;
  input Connector rhs;
  input SourceInfo info;
protected
  String lhs_str, rhs_str;
algorithm
  lhs_str := ComponentReference.printComponentRefStr(lhs.name);
  rhs_str := ComponentReference.printComponentRefStr(rhs.name);
  Error.addSourceMessageAndFail(Error.CONNECT_TWO_SOURCES,
    {lhs_str, rhs_str}, info);
end printConnectDirectionError;

protected function isSignalSource
  input Connector conn;
  output Boolean isSource;
protected
  Connect.ConnectorAttr attr = conn.attr;
algorithm
  isSource := match (attr.direction, conn.face, attr.visibility)
    case (DAE.OUTPUT(), Connect.INSIDE(), _) then true;
    case (DAE.INPUT(), Connect.OUTSIDE(), DAE.PUBLIC()) then true;
    else false;
  end match;
end isSignalSource;

//public function isReferenceInConnects
//  input list<ConnectorElement> connects;
//  input DAE.ComponentRef cref;
//  output Boolean isThere = false;
//algorithm
//  for ce in connects loop
//    if ComponentReference.crefPrefixOf(cref, ce.name) then
//      isThere := true;
//      return;
//    end if;
//  end for;
//end isReferenceInConnects;
//
//public function removeReferenceFromConnects
//  input output list<ConnectorElement> connects;
//  input DAE.ComponentRef cref;
//  output Boolean wasRemoved;
//protected
//  Option<ConnectorElement> oe;
//algorithm
//  (connects, oe) := List.deleteMemberOnTrue(cref, connects,
//    removeReferenceFromConnects2);
//  wasRemoved := isSome(oe);
//end removeReferenceFromConnects;
//
//protected function removeReferenceFromConnects2
//  input DAE.ComponentRef cref;
//  input ConnectorElement element;
//  output Boolean matches;
//algorithm
//  matches := ComponentReference.crefPrefixOf(cref, element.name);
//end removeReferenceFromConnects2;

public function isConstOrComplexConnector
  input Connector conn;
  output Boolean isConstOrComplex;
algorithm
  isConstOrComplex := match conn
    local
      DAE.VarKind var;

    case Connector.CONNECTOR(ty = DAE.T_COMPLEX()) then true;
    case Connector.CONNECTOR(attr = ConnectorAttr.CONN_ATTR(variability = var))
      then DAEUtil.isParamOrConstVarKind(var);

  end match;
end isConstOrComplexConnector;

public function isExpandableConnector
  "Returns true if the connector is an expandable connector."
  input Connector conn;
  output Boolean isExpandable = Types.isComplexExpandableConnector(conn.ty);
end isExpandableConnector;

public function isUndeclaredConnector
  "Returns true if the connector is undeclared, i.e. a connector that will be
   added to an expandable connector, otherwise false."
  input Connector conn;
  output Boolean isUndeclared;
algorithm
  isUndeclared := match conn
    case Connector.CONNECTOR(ty = DAE.T_UNKNOWN()) then true;
    else false;
  end match;
end isUndeclaredConnector;

public function associateFlowStream
  input ClassInf.State state;
  input String name;
  input SourceInfo info;
  input output DAE.DAElist dae;
protected
  list<DAE.Element> flows = {};
  Boolean has_stream = false;
  DAE.ComponentRef flow_name;
algorithm
  // Skip the function if the state doesn't indicate a connector.
  if not ClassInf.isConnector(state) then
    return;
  end if;

  // Collect all the flow variables in the dae, and check if there are any
  // stream variables.
  for e in dae.elementLst loop
    _ := match e
      case DAE.VAR(connectorType = ConnectorType.FLOW())
        algorithm
          flows := e :: flows;
        then
          ();

      case DAE.VAR(connectorType = ConnectorType.STREAM())
        algorithm
          has_stream := true;
        then
          ();

      else ();
    end match;
  end for;

  // Nothing to do if the connector doesn't have any stream variables.
  if not has_stream then
    return;
  end if;

  // A stream connector must have exactly one flow variable.
  if listLength(flows) <> 1 then
    Error.addSourceMessage(Error.UNBALANCED_STREAM_CONNECTOR,
      {name, String(listLength(flows))}, info);
    fail();
  end if;

  // Fetch the name of the single flow variable.
  {DAE.VAR(componentRef = flow_name)} := flows;

  // Finally, add the flow variable name to each stream variable in the dae.
  dae.elementLst := list(addFlowAssociation(e, flow_name) for e in dae.elementLst);
end associateFlowStream;

protected function addFlowAssociation
  input output DAE.Element element;
  input DAE.ComponentRef flowName;
algorithm
  _ := match element
    case DAE.VAR(connectorType = ConnectorType.STREAM())
      algorithm
        element.connectorType := ConnectorType.STREAM(SOME(flowName));
      then
        ();

    else ();
  end match;
end addFlowAssociation;

public function checkStreamConnector
  input ClassInf.State state;
  input list<tuple<SCode.Element, DAE.Mod>> components;
  input SourceInfo info;
  output Option<DAE.ComponentRef> flowName;
protected
  list<String> flows = {};
  Boolean has_stream = false;
  SCode.Element comp;
  Absyn.Path class_path;
algorithm
  if not ClassInf.isConnector(state) then
    flowName := NONE();
    return;
  end if;

  for c in components loop
    (comp, _) := c;
    _ := match comp
      case SCode.COMPONENT(attributes = SCode.ATTR(connectorType = SCode.FLOW()))
        algorithm
          flows := comp.name :: flows;
        then
          ();
      case SCode.COMPONENT(attributes = SCode.ATTR(connectorType = SCode.STREAM()))
        algorithm
          has_stream := true;
        then
          ();
      else ();
    end match;
  end for;

  if not has_stream then
    flowName := NONE();
    return;
  end if;

  if listLength(flows) <> 1 then
    ClassInf.CONNECTOR(path = class_path) := state;
    Error.addSourceMessage(Error.UNBALANCED_STREAM_CONNECTOR,
      {Absyn.pathString(class_path), String(listLength(flows))}, info);
    fail();
  end if;

  flowName := SOME(ComponentReference.makeUntypedCrefIdent(listHead(flows)));
end checkStreamConnector;

public function connectorStr
  input Connector conn;
  output String string;
protected
  DAE.ComponentRef name;
  Face face;
  ConnectorType cty;
  String name_str, face_str, cty_str;
algorithm
  name_str := ComponentReference.printComponentRefStr(conn.name);
  face_str := faceStr(conn.face);
  cty_str := connectorTypeStr(conn.cty);
  string := cty_str + " " + name_str + "<" + face_str + ">";
end connectorStr;

public function faceStr
  input Face face;
  output String string;
algorithm
  string := match face
    case Face.INSIDE() then "inside";
    case Face.OUTSIDE() then "outside";
    case Face.NO_FACE() then "no_face";
  end match;
end faceStr;

public function connectorTypeStr
  input DAE.ConnectorType connectorType;
  output String string;
algorithm
  string := match connectorType
    local
      DAE.ComponentRef cref;
      String cref_str;

    case ConnectorType.POTENTIAL() then "";
    case ConnectorType.FLOW() then "flow";
    case ConnectorType.STREAM(NONE()) then "stream()";
    case ConnectorType.STREAM(SOME(cref))
      algorithm
        cref_str := ComponentReference.printComponentRefStr(cref);
      then
        "stream(" + cref_str + ")";
    else "NOT_CONNECTOR";
  end match;
end connectorTypeStr;

public function unparseConnectorType
  input DAE.ConnectorType connectorType;
  output String string;
algorithm
  string := match connectorType
    case ConnectorType.FLOW() then "flow";
    case ConnectorType.STREAM(_) then "stream";
    else "";
  end match;
end unparseConnectorType;

annotation(__OpenModelica_Interface="frontend");
end ConnectUtil;
