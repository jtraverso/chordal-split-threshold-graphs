/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

module

public import GraphClassesLib.PaperIVCliqueTree.Basic
public import GraphClassesLib.PaperIVCliqueTree.Characterization
public import GraphClassesLib.PaperIVCliqueTree.Counting
public import GraphClassesLib.PaperIVCliqueTree.Gavril
public import GraphClassesLib.PaperIVCliqueTree.GluingChordal
public import GraphClassesLib.PaperIVCliqueTree.GluingCounting
public import GraphClassesLib.PaperIVCliqueTree.Helly
public import GraphClassesLib.PaperIVCliqueTree.Maximal
public import GraphClassesLib.PaperIVCliqueTree.MaximalBridge
public import GraphClassesLib.PaperIVCliqueTree.PEO
public import GraphClassesLib.PaperIVCliqueTree.Separator
public import GraphClassesLib.PaperIVCliqueTree.TreewidthExact

/-!
# Clique trees, subtree representations and chordal treewidth

Source: url:https://github.com/jtraverso/erdos-81-chordal-clique-partitions
Authors: Juan Pablo Traverso Gianini
Status: verified
Main declarations: `SimpleGraph.isChordal_iff_nonempty_subtreeRepresentation`
Tags: graph-theory, chordal-graphs, clique-trees, perfect-elimination-orders, separators
MSC: 05C75
-/
