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

encapsulated package ConnectionSets
" file:        ConnectionSets.mo
  package:     ConnectionSets
  description: Data structure and utilities to store connection sets.
"

public
import BaseHashTable;
import Connect;
import DAE;

protected
import Array;
import ComponentReference;
import ConnectUtil;
import Debug;
import ElementSource;
import Flags;
import List;
import System;
import Util;

public
import Connect.Connector;
import Connect.Connection;

protected
import MetaModelica.Dangerous.arrayCreateNoInit;

public
uniontype DisjointSets
  "This is a disjoint sets data structure. The nodes are stored in an array of
   Integers. The root elements of a set is given a negative value that
   corresponds to its rank, while other elements are given positive values that
   corresponds to the index of their parent in the array. The hashtable is used
   to look up the array index of a connector, and is also used to store the
   connectors."

  record DISJOINT_SETS
    array<Integer> nodes "An array of nodes";
    IndexTable elements "A Connector->Integer hashtable, see bottom of file.";
    Integer nodeCount "The number of nodes stored in the sets.";
  end DISJOINT_SETS;
end DisjointSets;

public
function emptySets
  "Creates a new disjoint-sets structure."
  input Integer connectionCount;
  output DisjointSets sets;
protected
  array<Integer> nodes;
  IndexTable elements;
  Integer sz;
algorithm
  // Create an array as large as the number of connections given, or at least 3
  // to avoid issues.
  sz := max(connectionCount, 3);
  // Fill the array with -1, which is the value of a newly added element.
  nodes := arrayCreate(sz, -1);
  elements := emptyIndexTableSized(Util.nextPrime(sz));
  sets := DISJOINT_SETS(nodes, elements, 0);
end emptySets;

function fromConnections
  "Creates a new DisjointSets from a list of connection and flow variables."
  input list<Connection> connections;
  input list<Connector> flowVariables;
  output DisjointSets sets;
algorithm
  // Approximate the size of the sets using the connections and flow variables.
  sets := emptySets(listLength(connections) + listLength(flowVariables));

  // Add flow variable to the sets, unless disabled by flag.
  if not Flags.isSet(Flags.DISABLE_SINGLE_FLOW_EQ) then
    sets := List.fold(flowVariables, addConnector, sets);
  end if;

  // Add the connections.
  sets := List.fold(connections, addConnection, sets);
end fromConnections;

function addConnector
  "Adds a connector as a node in the disjoint-sets forest. This function assumes
   that the node does not already exist. If the node might exist already, use
   find to add it instead."
  input Connector conn;
  input output DisjointSets sets;
protected
  list<Connector> expanded_conn;
  array<Integer> nodes;
  IndexTable elements;
  Integer node_count;
algorithm
  // Expand the connector into scalar connectors.
  expanded_conn := ConnectUtil.expandConnector(conn);
  DISJOINT_SETS(nodes, elements, node_count) := sets;

  // Make sure that we have enough space in the node array. Fill new elements
  // with -1 so we don't need to update the array when adding new nodes.
  if node_count + listLength(expanded_conn) > arrayLength(nodes) then
    nodes := Array.expand(arrayLength(nodes) + listLength(expanded_conn), nodes, -1);
  end if;

  // Add the scalar connectors to the index table.
  for c in expanded_conn loop
    node_count := node_count + 1;
    elements := BaseHashTable.addNoUpdCheck((c, node_count), elements);
  end for;

  sets := DISJOINT_SETS(nodes, elements, node_count);
end addConnector;

function addConnection
  "Adds a connection to the sets, which means merging the two sets that the
   connectors belong to, unless they already belong to the same set."
  input Connection connection;
  input output DisjointSets sets;
protected
  list<Connector> lhs_connl, rhs_connl, lhs_connl2, rhs_connl2;
  Connector c2, lhs = connection.lhs, rhs = connection.rhs;
  SourceInfo info = connection.info;
  DAE.ElementSource source;
algorithm
  source := ElementSource.createElementSource(info, NONE(), Prefix.NOPRE(), (lhs.name, rhs.name));
  lhs_connl := ConnectUtil.preExpandConnector(lhs);
  rhs_connl := ConnectUtil.preExpandConnector(rhs);

  for c1 in lhs_connl loop
    c2 :: rhs_connl := rhs_connl;
    ConnectUtil.checkConnectTypes(c1, c2, info);

    lhs_connl2 := ConnectUtil.expandConnector(c1);
    rhs_connl2 := ConnectUtil.expandConnector(c2);

    for c1 in lhs_connl2 loop
      c2 :: rhs_connl2 := rhs_connl2;
      sets := merge(c1, c2, sets);
    end for;
  end for;
end addConnection;

function findSet
  "This function finds and returns the set that the given connectors belongs to.
   The set is represented by the root node of the tree. If the connector does
   not have a corresponding node in the forest, then a new set with the
   connector as the only element will be added to the forest and returned.

   The reason why this function also returns the sets is because it does path
   compression, and the disjoint-set structure may therefore be changed during
   look up."
  input Connector conn;
  input DisjointSets sets;
  output Integer set;
  output DisjointSets updatedSets;
protected
  Integer index;
algorithm
  // Look up the index of the connector.
  (updatedSets, index) := find(conn, sets);
  // Return the index of the root of the tree that the connector belongs to.
  set := findRoot(index, updatedSets.nodes);
end findSet;

function findSetArrayIndex
  "Returns the index of the set the connector belongs to, or fails if the
   connector doesn't belong to a set."
  input Connector conn;
  input DisjointSets sets;
  output Integer set;
algorithm
  // Look up the index of the given connector.
  set := BaseHashTable.get(conn, sets.elements);

  // Follow the indices until a negative index is found, which is the set index.
  while set > 0 loop
    set := sets.nodes[set];
  end while;

  // Negate the index to get the actual set index.
  set := -set;
end findSetArrayIndex;

function merge
  "Merges the two sets that the given connectors belong to."
  input Connector connector1;
  input Connector connector2;
  input output DisjointSets sets;
protected
  Integer set1, set2;
algorithm
  (set1, sets) := findSet(connector1, sets);
  (set2, sets) := findSet(connector2, sets);
  sets := union(set1, set2, sets);
end merge;

function getNodeCount
  "Returns the number of nodes in the disjoint-set forest."
  input DisjointSets sets;
  output Integer nodeCount = sets.nodeCount;
end getNodeCount;

function extractSets
  "Extracts all the sets from the disjoint sets structure, and returns
   them as an array. The function also returns a new DisjointSets structure where
   all roots have been assigned a set index, which can be used for looking up
   sets in the array with findSetArrayIndex."
  input DisjointSets sets;
  output array<list<Connector>> setsArray "An array with all the sets.";
  output DisjointSets assignedSets "DisjointSets with the roots assigned to sets.";
protected
  array<Integer> nodes;
  Integer set_idx = 0, idx;
  list<tuple<Connector, Integer>> entries;
  Connector c;
algorithm
  nodes := sets.nodes;

  // Go through each node and assign a unique set index to each root node.
  // The index is stored as a negative number to mark the node as a root.
  for i in 1:sets.nodeCount loop
    if nodes[i] < 0 then
      set_idx := set_idx + 1;
      nodes[i] := -set_idx;
    end if;
  end for;

  // Create an array of lists to store the sets in, and fetch the list of
  // connector-index pairs stored in the hashtable.
  setsArray := arrayCreate(set_idx, {});
  entries := BaseHashTable.hashTableListReversed(sets.elements);

  // Go through each connector-index pair.
  for e in entries loop
    (c, idx) := e;
    // Follow the parent indices until we find the root.
    set_idx := nodes[idx];

    while set_idx > 0 loop
      set_idx := nodes[set_idx];
    end while;

    // Negate the set index to get the actual index.
    set_idx := -set_idx;
    // Add the connector to the list pointed to by the set index.
    setsArray[set_idx] := c :: setsArray[set_idx];
  end for;

  assignedSets := DisjointSets.DISJOINT_SETS(nodes, sets.elements, sets.nodeCount);
end extractSets;

function printSets
  "Print out the sets for debugging."
  input DisjointSets sets;
protected
  array<Integer> nodes;
  list<tuple<Connector, Integer>> entries;
  Connector c;
  Integer i;
algorithm
  print(intString(sets.nodeCount) + " sets:\n");
  nodes := sets.nodes;
  entries := BaseHashTable.hashTableList(sets.elements);

  for e in entries loop
    (c, i) := e;
    print("[");
    print(String(i));
    print("]");
    print(ConnectUtil.connectorStr(c));
    print(" -> ");
    print(String(nodes[i]));
    print("\n");
  end for;
end printSets;

protected
function addScalarConnector
  "Adds a connector which is known to be scalar (i.e. doesn't need to be
   expanded) to the sets. This function assumes that the node does not already
   exist. If the node might exist already, use find to add it instead."
  input Connector conn;
  input output DisjointSets sets;
        output Integer index;
algorithm
  // Increase the node count and use that as the node index.
  index := sets.nodeCount + 1;
  sets.nodeCount := index;

  // Make sure that we have space available in the node array. Fill new elements
  // with -1 so we don't need to update it when adding new nodes.
  if index > arrayLength(sets.nodes) then
    sets.nodes := Array.expand(arrayLength(sets.nodes), sets.nodes, -1);
  end if;

  // Register the node index in the index table.
  sets.elements := BaseHashTable.addNoUpdCheck((conn, index), sets.elements);
end addScalarConnector;

function find
  "This function finds and returns the node associated with a given connector.
   If the connector does not a have a node in the forest, then a new node will
   be added and returned.

   The reason why this function also returns the sets is because it does path
   compression, and the disjoint-set structure may therefore be changed during
   look up."
  input Connector conn;
  input output DisjointSets sets;
        output Integer index;
algorithm
  try
    // Check if a node already exists in the forest.
    index := BaseHashTable.get(conn, sets.elements);
  else
    // If a node doesn't already exist, create a new one.
    (sets, index) := addScalarConnector(conn, sets);
  end try;
end find;

function findRoot
  "Returns the index of the root of the tree that a node belongs to."
  input Integer nodeIndex;
  input array<Integer> nodes;
  output Integer rootIndex = nodeIndex;
protected
  Integer parent = nodes[nodeIndex], idx = nodeIndex;
algorithm
  // Follow the parent indices until we find a negative one, which indicates a root.
  while parent > 0 loop
    rootIndex := parent;
    parent := nodes[parent];
  end while;

  // Path compression. Attach each of the traversed nodes directly to the root,
  // to speed up repeated calls.
  parent := nodes[nodeIndex];
  while parent > 0 loop
    arrayUpdate(nodes, idx, rootIndex);
    idx := parent;
    parent := nodes[parent];
  end while;
end findRoot;

function union
  "Merges two sets into one. This is done by attaching one set-tree to the
   other. The ranks are compared to determine which of the trees is the
   smallest, and that one is attached to the larger one to keep the trees as
   flat as possible."
  input Integer set1;
  input Integer set2;
  input output DisjointSets sets;
protected
  Integer rank1, rank2;
algorithm
  if set1 <> set2 then
    // Assume that the indices actually point to root nodes, in which case the
    // entries in the node array is actually the ranks of the nodes.
    rank1 := sets.nodes[set1];
    rank2 := sets.nodes[set2];

    if rank1 > rank2 then
      // First set is smallest, attach it to the second set.
      arrayUpdate(sets.nodes, set2, set1);
    elseif rank1 < rank2 then
      // Second set is smallest, attach it to the first set.
      arrayUpdate(sets.nodes, set1, set2);
    else
      // Both sets are the same size. Attach the second to the first, and
      // increase the rank of the first with one (which means decreasing it,
      // since the rank is stored as a negative number).
      arrayUpdate(sets.nodes, set1, sets.nodes[set1] - 1);
      arrayUpdate(sets.nodes, set2, set1);
    end if;
  end if;
end union;

// Hashtable used by the DisjointSets structure.
public
type HashKey = Connector;
type HashValue = Integer;

type IndexTable = tuple<
  array<list<tuple<HashKey, Integer>>>,
  tuple<Integer, Integer, array<Option<tuple<HashKey, HashValue>>>>,
  Integer, tuple<FuncHash, FuncEq, FuncKeyString, FuncValString>
>;

partial function FuncHash
  input HashKey key;
  input Integer mod;
  output Integer hash;
end FuncHash;

partial function FuncEq
  input HashKey key1;
  input HashKey key2;
  output Boolean res;
end FuncEq;

partial function FuncKeyString
  input HashKey key;
  output String str;
end FuncKeyString;

partial function FuncValString
  input HashValue val;
  output String str;
end FuncValString;

protected
function connectorHashFunc
  "Hashes a connector."
  input Connector conn;
  input Integer mod;
  output Integer hash;
protected
  String cref_str;
algorithm
  /***************************************************************************/
  // TODO: Check if it's better for connectors with different faces to have
  // different hashes or not. Is one way more efficient than the other?
  /***************************************************************************/
  cref_str := ComponentReference.printComponentRefStr(conn.name);
  hash := System.stringHashDjb2Mod(cref_str, mod);
end connectorHashFunc;

function emptyIndexTableSized
  "Creates an empty index table with the given size."
  input Integer tableSize;
  output IndexTable table;
algorithm
  table := BaseHashTable.emptyHashTableWork(tableSize,
    (connectorHashFunc, ConnectUtil.connectorEqual, ConnectUtil.connectorStr, intString));
end emptyIndexTableSized;

annotation(__OpenModelica_Interface="frontend");
end ConnectionSets;
