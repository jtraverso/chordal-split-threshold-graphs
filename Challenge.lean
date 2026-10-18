/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Chordal, split, threshold and cograph structure

Statements about structural classes of finite simple graphs. The definitions of the graph classes
are reproduced below verbatim from the library (`GraphClassesLib/`), with the same names, so that
the comparator checks them as well as the theorems.

**Chordal graphs** (every cycle of length at least four has a chord):

* `ChordalClasses.minimalSeparator_isClique`: **Dirac (1961).** In a chordal graph every finite
  minimal `a`–`b` separator is a clique.
* `ChordalClasses.exists_isSimplicial`: **Dirac (1961).** A nonempty finite chordal graph has a
  simplicial vertex.
* `ChordalClasses.exists_two_nonadj_isSimplicial`: **Dirac (1961).** A connected, non-complete
  finite chordal graph has two non-adjacent simplicial vertices.
* `ChordalClasses.isChordal_iff_exists_isPEO`: **Fulkerson–Gross (1965).** A finite graph is
  chordal if and only if it has a perfect elimination order.
* `ChordalClasses.isChordal_iff_nonempty_subtreeRepresentation`: **Gavril (1974).** A finite graph
  is chordal if and only if it is the intersection graph of a family of subtrees of a finite tree.
* `ChordalClasses.treewidth_succ_eq_cliqueNum`: a nonempty finite chordal graph has treewidth
  `ω(G) − 1`; `ChordalClasses.cliqueNum_le_treewidth_succ`: every finite graph has
  `ω(G) ≤ tw(G) + 1`.

**Split, threshold and cograph classes:**

* `ChordalClasses.isSplit_iff_isChordal_and_compl`: **Földes–Hammer (1977).** A finite graph is
  split if and only if it and its complement are chordal.
* `ChordalClasses.isSplit_iff_forbidden_induced_subgraphs`: **Földes–Hammer (1977).** A finite
  graph is split if and only if it has no induced `2K₂`, `C₄` or `C₅`.
* `ChordalClasses.isCograph_iff_not_pathGraph_four_isIndContained`: cographs (graphs with no
  induced four-vertex path, `IsP4Free`) are exactly the graphs with no induced `P₄` in Mathlib's
  sense.
* `ChordalClasses.isThreshold_iff_isSplit_and_isCograph`: threshold graphs (split graphs whose
  independent vertices have nested neighbourhoods) are exactly the split cographs.
* `ChordalClasses.isThreshold_iff_forbidden_induced_subgraphs`: **Chvátal–Hammer (1977).** A finite
  graph is threshold if and only if it has no induced `2K₂`, `C₄` or `P₄`.

Induced subgraphs, `pathGraph`, `cycleGraph`, the disjoint union `⊕g`, cliques, independent sets,
trees and the clique number `cliqueNum` are Mathlib's.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

/-! ## Definitions (verbatim from the library) -/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A graph is **chordal** if every cycle of length `≥ 4` has a chord: an adjacency between two
vertices of the cycle whose edge is not one of the cycle's own edges. -/
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ ⦃v : V⦄ (c : G.Walk v v), c.IsCycle → 4 ≤ c.length →
    ∃ x y : V, x ∈ c.support ∧ y ∈ c.support ∧ G.Adj x y ∧ s(x, y) ∉ c.edges

/-- A vertex is **simplicial** if its neighbourhood induces a clique. -/
def IsSimplicial (G : SimpleGraph V) (v : V) : Prop := G.IsClique (G.neighborSet v)

/-- `S` **separates** `a` from `b` if neither lies in `S` and every walk `a → b` meets `S`. -/
def Separates (G : SimpleGraph V) (S : Set V) (a b : V) : Prop :=
  a ∉ S ∧ b ∉ S ∧ ¬ Relation.ReflTransGen (fun p q => p ∉ S ∧ q ∉ S ∧ G.Adj p q) a b

/-- `S` is a **minimal** `a`–`b` separator: it separates them and no proper subset does. -/
def IsMinimalSeparator (G : SimpleGraph V) (S : Set V) (a b : V) : Prop :=
  G.Separates S a b ∧ ∀ T ⊂ S, ¬ G.Separates T a b

end SimpleGraph

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A **perfect elimination order** of `G`, given by an injective ranking `ord : V → ℕ`: the
neighbours of a vertex that come later in the order form a clique. -/
structure IsPEO (G : SimpleGraph V) (ord : V → ℕ) : Prop where
  /-- The ranking is injective, i.e. it is a linear order on the vertices. -/
  injective : Function.Injective ord
  /-- The later neighbourhood of every vertex is a clique. -/
  isClique_later : ∀ v : V, G.IsClique {u | ord v < ord u ∧ G.Adj v u}

end SimpleGraph

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- An exact representation by nonempty connected vertex sets of a finite tree. -/
structure SubtreeRepresentation (G : SimpleGraph V) where
  /-- Vertices of the host tree. -/
  Node : Type
  [nodeFintype : Fintype Node]
  /-- The host tree. -/
  tree : SimpleGraph Node
  /-- The host is connected and acyclic. -/
  isTree : tree.IsTree
  /-- The subtree assigned to each graph vertex. -/
  subtree : V → Set Node
  /-- Every assigned subtree is connected, hence nonempty. -/
  connected : ∀ v, (tree.induce (subtree v)).Connected
  /-- Distinct vertices are adjacent exactly when their subtrees intersect. -/
  adjacency : ∀ u v, u ≠ v → (G.Adj u v ↔ (subtree u ∩ subtree v).Nonempty)

attribute [instance] SubtreeRepresentation.nodeFintype

end SimpleGraph

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V}

/-- A partition of the vertices into a clique and an independent set. -/
structure SplitPartition (G : SimpleGraph V) where
  /-- The clique part. -/
  clique : Set V
  /-- The independent part. -/
  independent : Set V
  /-- The clique part induces a complete graph. -/
  isClique : G.IsClique clique
  /-- The independent part contains no edges. -/
  isIndepSet : G.IsIndepSet independent
  /-- No vertex belongs to both parts. -/
  disjoint : Disjoint clique independent
  /-- Every vertex belongs to one of the parts. -/
  cover : clique ∪ independent = Set.univ

/-- A graph is split if it admits a split partition. -/
def IsSplit (G : SimpleGraph V) : Prop := Nonempty (SplitPartition G)

end SimpleGraph

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V}

/-- There is no induced path on four vertices, in the order `a, b, c, d`. -/
def IsP4Free (G : SimpleGraph V) : Prop :=
  ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
    ¬G.Adj a c → ¬G.Adj a d → ¬G.Adj b d → False

end SimpleGraph

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

namespace SplitPartition

variable (P : SplitPartition G)

/-- The independent vertices have neighborhoods linearly ordered by inclusion. -/
def HasNestedNeighborhoods : Prop :=
  ∀ u ∈ P.independent, ∀ v ∈ P.independent,
    G.neighborSet u ⊆ G.neighborSet v ∨ G.neighborSet v ⊆ G.neighborSet u

end SplitPartition

/-- A threshold graph admits a split partition with nested independent neighborhoods. -/
def IsThreshold (G : SimpleGraph V) : Prop :=
  ∃ P : SplitPartition G, P.HasNestedNeighborhoods

end SimpleGraph

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Cographs are graphs with no induced four-vertex path. -/
def IsCograph (G : SimpleGraph V) : Prop := G.IsP4Free

end SimpleGraph

namespace Utilities.Treewidth

open Finset

universe u

variable {V : Type u}

/-- A **tree decomposition** of a simple graph `H`: a finite tree `tree` on a node type `Node`,
together with a `bag` of vertices at each node, such that every vertex lies in some bag, the two
endpoints of every edge lie in a common bag, and for each vertex `v` the set of nodes whose bag
contains `v` induces a connected (in particular nonempty) subtree. -/
structure TreeDecomposition (H : SimpleGraph V) where
  /-- The nodes of the decomposition tree. -/
  Node : Type
  [nodeFintype : Fintype Node]
  [nodeDecidableEq : DecidableEq Node]
  /-- The decomposition tree. -/
  tree : SimpleGraph Node
  /-- `tree` really is a tree: connected and acyclic. -/
  isTree : tree.IsTree
  /-- The bag of vertices sitting at each node. -/
  bag : Node → Finset V
  /-- Every vertex appears in some bag. -/
  cover_vertex : ∀ v : V, ∃ t, v ∈ bag t
  /-- Every edge has both endpoints in a common bag. -/
  cover_edge : ∀ v w : V, H.Adj v w → ∃ t, v ∈ bag t ∧ w ∈ bag t
  /-- The nodes containing a fixed vertex form a connected subtree. -/
  coherent : ∀ v : V, (tree.induce {t | v ∈ bag t}).Connected

attribute [instance] TreeDecomposition.nodeFintype TreeDecomposition.nodeDecidableEq

namespace TreeDecomposition

variable {H : SimpleGraph V}

/-- The **width** of a tree decomposition: one less than the largest bag size. -/
def width (D : TreeDecomposition H) : ℕ :=
  (Finset.univ.sup fun t : D.Node => (D.bag t).card) - 1

end TreeDecomposition

/-- The set of widths realized by some tree decomposition of `H`. -/
def widthSet (H : SimpleGraph V) : Set ℕ :=
  {w : ℕ | ∃ D : TreeDecomposition H, D.width = w}

/-- The **treewidth** of `H`: the least width of a tree decomposition. -/
noncomputable def treewidth (H : SimpleGraph V) : ℕ :=
  sInf (widthSet H)

end Utilities.Treewidth

/-! ## Statements -/

namespace ChordalClasses

open SimpleGraph

section

variable {V : Type*} {G : SimpleGraph V}

/-- **Dirac (1961).** In a chordal graph, every finite minimal separator of two fixed vertices is a
clique. -/
theorem minimalSeparator_isClique (hG : G.IsChordal) {S : Finset V} {a b : V}
    (hS : G.IsMinimalSeparator (S : Set V) a b) : G.IsClique (S : Set V) := by
  sorry

/-- **Dirac (1961).** A nonempty finite chordal graph has a simplicial vertex. -/
theorem exists_isSimplicial [Finite V] [Nonempty V] (hG : G.IsChordal) :
    ∃ v : V, G.IsSimplicial v := by
  sorry

/-- **Dirac (1961).** A connected non-complete finite chordal graph has two distinct non-adjacent
simplicial vertices. -/
theorem exists_two_nonadj_isSimplicial [Finite V] (hG : G.IsChordal) (hconn : G.Connected)
    (hnc : ¬ ∀ u v : V, u ≠ v → G.Adj u v) :
    ∃ x y : V, x ≠ y ∧ ¬ G.Adj x y ∧ G.IsSimplicial x ∧ G.IsSimplicial y := by
  sorry

/-- **Fulkerson–Gross (1965).** A finite graph is chordal if and only if it has a perfect
elimination order. -/
theorem isChordal_iff_exists_isPEO [Finite V] : G.IsChordal ↔ ∃ ord : V → ℕ, G.IsPEO ord := by
  sorry

/-- Every finite graph has clique number at most its treewidth plus one. -/
theorem cliqueNum_le_treewidth_succ [Finite V] (G : SimpleGraph V) :
    G.cliqueNum ≤ Utilities.Treewidth.treewidth G + 1 := by
  sorry

/-- **Földes–Hammer (1977).** A finite graph is split if and only if it and its complement are
chordal. -/
theorem isSplit_iff_isChordal_and_compl [Finite V] : G.IsSplit ↔ G.IsChordal ∧ Gᶜ.IsChordal := by
  sorry

/-- **Földes–Hammer (1977).** A finite graph is split if and only if it has no induced `2K₂`, `C₄`
or `C₅`. -/
theorem isSplit_iff_forbidden_induced_subgraphs [Finite V] :
    G.IsSplit ↔
      (¬((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsIndContained G) ∧
      (¬(cycleGraph 4).IsIndContained G) ∧ ¬(cycleGraph 5).IsIndContained G := by
  sorry

/-- Cographs (no induced four-vertex path) are exactly the graphs with no induced `P₄` in the
sense of Mathlib's induced containment. -/
theorem isCograph_iff_not_pathGraph_four_isIndContained :
    G.IsCograph ↔ ¬(pathGraph 4).IsIndContained G := by
  sorry

/-- Threshold graphs are exactly the split cographs. -/
theorem isThreshold_iff_isSplit_and_isCograph : G.IsThreshold ↔ G.IsSplit ∧ G.IsCograph := by
  sorry

/-- **Chvátal–Hammer (1977).** A finite graph is threshold if and only if it has no induced `2K₂`,
`C₄` or `P₄`. -/
theorem isThreshold_iff_forbidden_induced_subgraphs [Finite V] :
    G.IsThreshold ↔
      (¬((⊤ : SimpleGraph (Fin 2)) ⊕g (⊤ : SimpleGraph (Fin 2))).IsIndContained G) ∧
      (¬(cycleGraph 4).IsIndContained G) ∧ ¬(pathGraph 4).IsIndContained G := by
  sorry

end

section

variable {V : Type} {G : SimpleGraph V}

/-- **Gavril (1974).** A finite graph is chordal if and only if it is the intersection graph of a
family of subtrees of a finite tree. -/
theorem isChordal_iff_nonempty_subtreeRepresentation [Finite V] :
    G.IsChordal ↔ Nonempty (SubtreeRepresentation G) := by
  sorry

/-- A nonempty finite chordal graph has treewidth exactly its clique number minus one. -/
theorem treewidth_succ_eq_cliqueNum [Finite V] [Nonempty V] (hG : G.IsChordal) :
    Utilities.Treewidth.treewidth G + 1 = G.cliqueNum := by
  sorry

end

end ChordalClasses
