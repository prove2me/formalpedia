-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter31
-- name    : ProofsInTheBook_Chapter31
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T16:15:42.935822+00:00
-- url     : https://prove2.me/theorems/5d533f04-c822-4e5e-888a-16126b337f02
-- title:
--   Labeled trees, Prüfer codes, and rooted-tree maps
-- statement:
--   For a natural number $n$, a labeled tree is a connected acyclic simple graph on $\operatorname{Fin}(n)$. A Prüfer code is a sequence in
--   $$\operatorname{Fin}(n)^{\operatorname{Fin}(n-2)},$$
--   where $n-2$ is natural subtraction. For $n\ge2$, the encoding records neighbors during successive deletion of the smallest labeled leaf; the decoding uses the smallest remaining label absent from the unprocessed suffix, then joins the final two labels. The intermediate states consist of an edge forest and a set containing exactly one active representative from each component.
--
--   A doubly rooted labeled tree has two ordered distinguished vertices, which may coincide. The bundle represents its unique root-to-root path, both in path order and in increasing label order. The associated vertex map matches these orders on the path and sends an off-path vertex toward the first root. It also records the periodic vertices of a self-map, consecutive-pair adjacency in lists, and the corresponding recovered tree relation. These are definitions of combinatorial objects and maps; no tree-count formula is imposed in their definitions.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 33, “Cayley’s formula for the number of trees”, pp. 235–240 (https://doi.org/10.1007/978-3-662-57265-8_33). Original definition source: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter31.lean#L28. The generated bundle retains definitions and supporting declarations from this source; the book citation identifies their topic rather than asserting that each auxiliary structure appears in the book.

import Mathlib
set_option autoImplicit true


/-!
# Chapter 31: Cayley's formula for the number of trees

From "Proofs from THE BOOK":

**Cayley's formula**: The number of labeled trees on n vertices is n^{n-2}.

The book presents multiple proofs:
1. Prüfer sequences (bijection with [n]^{n-2}).
2. A double counting argument on labeled rooted forests.
3. The determinant formula via Kirchhoff's matrix tree theorem.
-/

namespace ProofsInTheBook.Chapter31

open SimpleGraph

/-!
### Prüfer-code counting side

The Prüfer proof of Cayley's formula builds a bijection between labeled trees
on `n` vertices and words of length `n - 2` over an `n`-letter alphabet.  This
file records the finite counting side of that target code space.
-/

abbrev pruferCodeSpace (n : ℕ) : Type :=
  Fin (n - 2) → Fin n

/-- Labeled trees on vertex set `Fin n`. -/
abbrev LabeledTree (n : ℕ) : Type :=
  {G : SimpleGraph (Fin n) // G.IsTree}

noncomputable instance (n : ℕ) : Fintype (LabeledTree n) := by
  classical
  dsimp [LabeledTree]
  infer_instance

noncomputable instance (n : ℕ) : DecidableEq (LabeledTree n) := by
  classical
  exact Classical.decEq _

theorem isTree_induce_compl_singleton_of_degree_eq_one
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {v : V}
    (hG : G.IsTree) (hdeg : G.degree v = 1) :
    (G.induce ({v}ᶜ : Set V)).IsTree := by
  exact ⟨hG.connected.induce_compl_singleton_of_degree_eq_one hdeg,
    hG.isAcyclic.induce ({v}ᶜ : Set V)⟩

theorem existsUnique_adj_of_degree_eq_one
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {v : V}
    (hdeg : G.degree v = 1) :
    ∃! w, G.Adj v w :=
  SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg



noncomputable def treeLeaves (T : LabeledTree n) : Finset (Fin n) :=
  by
    classical
    exact Finset.univ.filter fun v => ∃! w, T.1.Adj v w

theorem treeLeaves_nonempty (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) :
    (treeLeaves T).Nonempty := by
  classical
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨v, hv⟩ := T.2.exists_vert_degree_one_of_nontrivial
  have hv' : ∃! w, T.1.Adj v w :=
    existsUnique_adj_of_degree_eq_one hv
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv'⟩⟩

noncomputable def smallestTreeLeaf (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) : Fin n :=
  (treeLeaves T).min' (treeLeaves_nonempty n hn T)

theorem smallestTreeLeaf_mem_leaves (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) :
    smallestTreeLeaf n hn T ∈ treeLeaves T :=
  Finset.min'_mem _ _

theorem unique_adj_smallestTreeLeaf (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) :
    ∃! w, T.1.Adj (smallestTreeLeaf n hn T) w := by
  have hmem := smallestTreeLeaf_mem_leaves n hn T
  simpa [treeLeaves] using hmem



noncomputable def smallestTreeLeafNeighbor (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) : Fin n :=
  (ExistsUnique.exists (unique_adj_smallestTreeLeaf n hn T)).choose





theorem isTree_delete_smallestTreeLeaf (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) :
    (T.1.induce ({smallestTreeLeaf n hn T}ᶜ : Set (Fin n))).IsTree := by
  classical
  let leaf := smallestTreeLeaf n hn T
  change (T.1.induce ({leaf}ᶜ : Set (Fin n))).IsTree
  letI : Fintype (T.1.neighborSet leaf) :=
    Subtype.fintype fun w => w ∈ T.1.neighborSet leaf
  have hdeg : T.1.degree leaf = 1 :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr (unique_adj_smallestTreeLeaf n hn T)
  exact isTree_induce_compl_singleton_of_degree_eq_one T.2 hdeg

noncomputable def finSuccAboveEquivCompl {m : ℕ} (leaf : Fin (m + 1)) :
    Fin m ≃ {v : Fin (m + 1) // v ∈ ({leaf}ᶜ : Set (Fin (m + 1)))} := by
  classical
  refine Equiv.ofBijective (fun i => ⟨leaf.succAbove i, by simp⟩) ?_
  constructor
  · intro i j hij
    exact leaf.succAbove_right_injective (congrArg Subtype.val hij)
  · intro v
    have hvNotMem : v.1 ∉ ({leaf} : Set (Fin (m + 1))) := v.2
    have hv : v.1 ≠ leaf := by
      intro h
      exact hvNotMem (by simp [h])
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hv
    exact ⟨i, Subtype.ext hi⟩

noncomputable def deleteSmallestLeafTreeSucc (m : ℕ) (hm : 1 ≤ m)
    (T : LabeledTree (m + 1)) : LabeledTree m := by
  classical
  have hn : 2 ≤ m + 1 := by omega
  let leaf := smallestTreeLeaf (m + 1) hn T
  let e := finSuccAboveEquivCompl leaf
  refine ⟨(T.1.induce ({leaf}ᶜ : Set (Fin (m + 1)))).comap e.toEmbedding, ?_⟩
  have hdel : (T.1.induce ({leaf}ᶜ : Set (Fin (m + 1)))).IsTree := by
    simpa [leaf] using isTree_delete_smallestTreeLeaf (m + 1) hn T
  exact (SimpleGraph.Iso.isTree_iff
    (SimpleGraph.Iso.comap e (T.1.induce ({leaf}ᶜ : Set (Fin (m + 1)))))).mpr hdel

/-- A labeled tree with two distinguished vertices, the object counted in Joyal's proof. -/
abbrev DoublyRootedLabeledTree (n : ℕ) : Type :=
  LabeledTree n × Fin n × Fin n

noncomputable def treePath (T : LabeledTree n) (u v : Fin n) : T.1.Walk u v :=
  (ExistsUnique.exists (T.2.existsUnique_path u v)).choose

theorem treePath_isPath (T : LabeledTree n) (u v : Fin n) :
    (treePath T u v).IsPath :=
  (ExistsUnique.exists (T.2.existsUnique_path u v)).choose_spec







noncomputable def joyalPathVertices (X : DoublyRootedLabeledTree n) : Finset (Fin n) :=
  (treePath X.1 X.2.1 X.2.2).support.toFinset

theorem joyal_left_mem_pathVertices (X : DoublyRootedLabeledTree n) :
    X.2.1 ∈ joyalPathVertices X := by
  exact List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support _)



/-- First row in Joyal's table: path vertices sorted by their labels. -/
noncomputable def joyalPathDomainOrder (X : DoublyRootedLabeledTree n) : List (Fin n) :=
  (joyalPathVertices X).sort (· ≤ ·)

/-- Second row in Joyal's table: the same path vertices in left-to-right path order. -/
noncomputable def joyalPathRangeOrder (X : DoublyRootedLabeledTree n) : List (Fin n) :=
  (treePath X.1 X.2.1 X.2.2).support

theorem joyalPathDomainOrder_nodup (X : DoublyRootedLabeledTree n) :
    (joyalPathDomainOrder X).Nodup := by
  exact (joyalPathVertices X).sort_nodup (· ≤ ·)

theorem joyalPathRangeOrder_nodup (X : DoublyRootedLabeledTree n) :
    (joyalPathRangeOrder X).Nodup := by
  simpa [joyalPathRangeOrder] using
    (SimpleGraph.Walk.isPath_def (treePath X.1 X.2.1 X.2.2)).mp
      (treePath_isPath X.1 X.2.1 X.2.2)



theorem joyalPathRangeOrder_toFinset (X : DoublyRootedLabeledTree n) :
    (joyalPathRangeOrder X).toFinset = joyalPathVertices X := by
  rfl

theorem joyalPathOrders_length_eq (X : DoublyRootedLabeledTree n) :
    (joyalPathDomainOrder X).length = (joyalPathRangeOrder X).length := by
  calc
    (joyalPathDomainOrder X).length = (joyalPathVertices X).card := by
      simp [joyalPathDomainOrder]
    _ = (joyalPathRangeOrder X).toFinset.card := by
      rw [joyalPathRangeOrder_toFinset]
    _ = (joyalPathRangeOrder X).length := by
      rw [List.toFinset_card_of_nodup (joyalPathRangeOrder_nodup X)]

/-- The path-row part of Joyal's inverse map: first-row vertex ↦ same-column second-row vertex. -/
noncomputable def joyalPathTableValue (X : DoublyRootedLabeledTree n)
    (v : Fin n) (hv : v ∈ joyalPathVertices X) : Fin n := by
  let domain := joyalPathDomainOrder X
  let range := joyalPathRangeOrder X
  have hvd : v ∈ domain := by
    simpa [domain, joyalPathDomainOrder] using hv
  let i : Fin domain.length :=
    (List.Nodup.getEquiv domain (by simpa [domain] using joyalPathDomainOrder_nodup X)).symm
      ⟨v, hvd⟩
  exact range.get ⟨i.1, by
    change i.1 < (joyalPathRangeOrder X).length
    rw [← joyalPathOrders_length_eq X]
    simp [domain]⟩

/-- For a vertex off the left-right path, point to the next vertex on its path toward the left end. -/
noncomputable def joyalOffPathValue (X : DoublyRootedLabeledTree n)
    (v : Fin n) (hv : v ∉ joyalPathVertices X) : Fin n := by
  let p := treePath X.1 v X.2.1
  have hne : v ≠ X.2.1 := by
    intro h
    subst h
    exact hv (joyal_left_mem_pathVertices X)
  have hp : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  exact p.snd











/-- Joyal's map from a doubly-rooted tree to an endofunction on its label set. -/
noncomputable def joyalTreeToFunction (X : DoublyRootedLabeledTree n) : Fin n → Fin n :=
  fun v =>
    if hv : v ∈ joyalPathVertices X then
      joyalPathTableValue X v hv
    else
      joyalOffPathValue X v hv

theorem joyalTreeToFunction_apply_of_mem (X : DoublyRootedLabeledTree n)
    {v : Fin n} (hv : v ∈ joyalPathVertices X) :
    joyalTreeToFunction X v = joyalPathTableValue X v hv := by
  simp [joyalTreeToFunction, hv]



noncomputable def periodicCore (f : Fin n → Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => ∃ m : ℕ, 0 < m ∧ f^[m] v = v



theorem joyalPathTableValue_mem_pathVertices (X : DoublyRootedLabeledTree n)
    {v : Fin n} (hv : v ∈ joyalPathVertices X) :
    joyalPathTableValue X v hv ∈ joyalPathVertices X := by
  classical
  unfold joyalPathTableValue
  simp only
  have hvd : v ∈ joyalPathDomainOrder X := by
    simpa [joyalPathDomainOrder] using hv
  have hidx : List.idxOf v (joyalPathDomainOrder X) <
      (treePath X.1 X.2.1 X.2.2).support.length := by
    have hdom : List.idxOf v (joyalPathDomainOrder X) < (joyalPathDomainOrder X).length :=
      List.idxOf_lt_length_iff.mpr hvd
    rwa [joyalPathOrders_length_eq X, joyalPathRangeOrder] at hdom
  change (treePath X.1 X.2.1 X.2.2).support[List.idxOf v (joyalPathDomainOrder X)]'hidx ∈
    (treePath X.1 X.2.1 X.2.2).support.toFinset
  exact List.mem_toFinset.mpr (List.get_mem (treePath X.1 X.2.1 X.2.2).support _)

theorem joyalTreeToFunction_maps_pathVertices (X : DoublyRootedLabeledTree n)
    {v : Fin n} (hv : v ∈ joyalPathVertices X) :
    joyalTreeToFunction X v ∈ joyalPathVertices X := by
  rw [joyalTreeToFunction_apply_of_mem X hv]
  exact joyalPathTableValue_mem_pathVertices X hv



noncomputable def joyalPathSelfMap (X : DoublyRootedLabeledTree n) :
    {v : Fin n // v ∈ joyalPathVertices X} → {v : Fin n // v ∈ joyalPathVertices X} :=
  fun v => ⟨joyalTreeToFunction X v.1, joyalTreeToFunction_maps_pathVertices X v.2⟩





































def adjacentInList (l : List (Fin n)) (u v : Fin n) : Prop :=
  ∃ i : ℕ, ∃ hi : i < l.length, ∃ hi' : i + 1 < l.length,
    (l[i]'hi = u ∧ l[i + 1]'hi' = v) ∨ (l[i]'hi = v ∧ l[i + 1]'hi' = u)





def joyalRecoveredAdj (X : DoublyRootedLabeledTree n) (u v : Fin n) : Prop :=
  adjacentInList (joyalPathRangeOrder X) u v ∨
    (u ∉ joyalPathVertices X ∧ joyalTreeToFunction X u = v) ∨
    (v ∉ joyalPathVertices X ∧ joyalTreeToFunction X v = u)































/-!
### Current target: eliminate the Cayley upper-bound premise

The book chapter (Chapter 30 in `proofs_in_the_book.pdf`, Chapter31 in this
repository) mentions Prüfer's code, then develops several alternate proofs:
Joyal's function-to-doubly-rooted-tree bijection, Kirchhoff's matrix-tree
proof, Riordan-Rényi recursion, and Pitman's double-counting proof for rooted
forests.

For this Lean file the immediate target is the upper bound needed to construct
an injection into Prüfer code space:

`Fintype.card (LabeledTree n) ≤ n ^ (n - 2)`.

This is isolated here as the single remaining mathematical target for the
chapter. The likely formalization route is still under evaluation:

* Prüfer encoding uses Mathlib's `SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial`
  and leaf deletion lemmas.
* The book's Joyal/Pitman proofs may avoid recursive graph deletion but require
  formalizing functional digraph cycles or rooted forests.
-/






/--
A vertex is a leaf of a tree iff it does not appear in its Prüfer code.
-/
def isLeafInPrufer (code : pruferCodeSpace n) (v : Fin n) : Prop :=
  ∀ i : Fin (n - 2), code i ≠ v

instance (code : pruferCodeSpace n) (v : Fin n) : Decidable (isLeafInPrufer code v) :=
  Fintype.decidableForallFintype







structure DecodeForestFull (n : ℕ) (state : Finset (Fin n) × Finset (Sym2 (Fin n))) : Prop where
  acyclic : (fromEdgeSet (state.2 : Set (Sym2 (Fin n)))).IsAcyclic
  covers : ∀ u : Fin n, ∃ v ∈ state.1, (fromEdgeSet (state.2 : Set _)).Reachable u v
  uniq : ∀ v ∈ state.1, ∀ w ∈ state.1, v ≠ w → ¬ (fromEdgeSet (state.2 : Set _)).Reachable v w

lemma decodeForest_init (n : ℕ) (_hn : 2 ≤ n) :
    DecodeForestFull n (Finset.univ, ∅) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u p hp
    have hne := hp.ne_nil
    cases p with
    | nil => exact False.elim (hne rfl)
    | cons hadj _ => simp at hadj
  · intro u
    exact ⟨u, Finset.mem_univ u, Walk.nil.reachable⟩
  · intro v _ w _ hvw hreach
    rcases hreach with ⟨walk⟩
    cases walk with
    | nil => exact hvw rfl
    | cons hadj _ => simp at hadj

lemma refl_symm {V : Type*} {G : SimpleGraph V} {x y : V}
    (h : Relation.ReflTransGen G.Adj x y) : Relation.ReflTransGen G.Adj y x :=
  (reachable_iff_reflTransGen y x).mp ((reachable_iff_reflTransGen x y).mpr h).symm

lemma reachable_sup_edge {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (hreach : Relation.ReflTransGen (G.Adj ⊔ (edge u v).Adj) x y) :
    Relation.ReflTransGen G.Adj x y ∨
    (Relation.ReflTransGen G.Adj x u ∧ Relation.ReflTransGen G.Adj v y) ∨
    (Relation.ReflTransGen G.Adj x v ∧ Relation.ReflTransGen G.Adj u y) := by
  induction hreach with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | tail h_trans h_adj ih =>
    rcases h_adj with (hG | hedge)
    · rcases ih with (ih1 | ⟨ih2u, ih2v⟩ | ⟨ih3v, ih3u⟩)
      · exact Or.inl (Relation.ReflTransGen.tail ih1 hG)
      · exact Or.inr (Or.inl ⟨ih2u, Relation.ReflTransGen.tail ih2v hG⟩)
      · exact Or.inr (Or.inr ⟨ih3v, Relation.ReflTransGen.tail ih3u hG⟩)
    · revert hedge
      simp [edge, Sym2.eq]
      intro hedge'
      rcases hedge' with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · intro _
        rcases ih with (ih1 | ⟨ih2u, ih2v⟩ | ⟨ih3v, ih3u⟩)
        · exact Or.inr (Or.inl ⟨ih1, Relation.ReflTransGen.refl⟩)
        · exact Or.inl (Relation.ReflTransGen.trans ih2u (refl_symm ih2v))
        · exact Or.inl ih3v
      · intro _
        rcases ih with (ih1 | ⟨ih2u, ih2v⟩ | ⟨ih3v, ih3u⟩)
        · exact Or.inr (Or.inr ⟨ih1, Relation.ReflTransGen.refl⟩)
        · exact Or.inl ih2u
        · exact Or.inl (Relation.ReflTransGen.trans ih3v (refl_symm ih3u))

lemma reachable_sup_edge_graph {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (hreach : (G ⊔ edge u v).Reachable x y) :
    G.Reachable x y ∨
    (G.Reachable x u ∧ G.Reachable v y) ∨
    (G.Reachable x v ∧ G.Reachable u y) := by
  have h1 := reachable_sup_edge (reachable_iff_reflTransGen x y |>.mp hreach)
  rcases h1 with (h2 | ⟨h3u, h3v⟩ | ⟨h4v, h4u⟩)
  · exact Or.inl (reachable_iff_reflTransGen x y |>.mpr h2)
  · exact Or.inr (Or.inl ⟨reachable_iff_reflTransGen x u |>.mpr h3u, reachable_iff_reflTransGen v y |>.mpr h3v⟩)
  · exact Or.inr (Or.inr ⟨reachable_iff_reflTransGen x v |>.mpr h4v, reachable_iff_reflTransGen u y |>.mpr h4u⟩)

lemma decodeForest_step {n : ℕ} {state : Finset (Fin n) × Finset (Sym2 (Fin n))}
    (h_forest : DecodeForestFull n state) (nextLeaf : Fin n) (hnL : nextLeaf ∈ state.1)
    (si : Fin n) (h_future : si ∈ state.1) (h_not_eq : nextLeaf ≠ si) :
    DecodeForestFull n (state.1.erase nextLeaf, insert s(nextLeaf, si) state.2) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [Prod.snd]
    have hsup : fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _) = fromEdgeSet (state.2 : Set _) ⊔ edge nextLeaf si := by
      ext a b; simp [fromEdgeSet, edge, Sym2.ToRel, Sym2.eq]; tauto
    rw [hsup]
    rw [isAcyclic_sup_fromEdgeSet_iff]
    refine ⟨h_forest.acyclic, ?_⟩
    intro hreach
    have h_not_reach := h_forest.uniq nextLeaf hnL si h_future h_not_eq
    exact False.elim (h_not_reach hreach)
  · intro u
    dsimp only [Prod.fst, Prod.snd]
    have hsup : fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _) = fromEdgeSet (state.2 : Set _) ⊔ edge nextLeaf si := by
      ext a b; simp [fromEdgeSet, edge, Sym2.ToRel, Sym2.eq]; tauto
    rcases h_forest.covers u with ⟨r, hr, hreach⟩
    by_cases h_r : r = nextLeaf
    · rw [h_r] at hreach
      have h_new_reach : (fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _)).Reachable u nextLeaf := by
        rw [hsup]
        exact hreach.mono le_sup_left
      have h_edge : (fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _)).Adj nextLeaf si := by
        rw [hsup]
        exact Or.inr ⟨by simp [Sym2.ToRel], h_not_eq⟩
      have h_si_reach := Reachable.trans h_new_reach (Adj.reachable h_edge)
      rcases h_forest.covers si with ⟨r', hr', hreach'⟩
      have h_r'_neq : r' ≠ nextLeaf := by
        intro heq
        rw [heq] at hreach'
        have h_not_reach := h_forest.uniq si h_future nextLeaf hnL h_not_eq.symm
        exact h_not_reach hreach'
      have h_r'_reach : (fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _)).Reachable si r' := by
        rw [hsup]
        exact hreach'.mono le_sup_left
      exact ⟨r', Finset.mem_erase_of_ne_of_mem h_r'_neq hr', Reachable.trans h_si_reach h_r'_reach⟩
    · have h_new_reach : (fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _)).Reachable u r := by
        rw [hsup]
        exact hreach.mono le_sup_left
      exact ⟨r, Finset.mem_erase_of_ne_of_mem h_r hr, h_new_reach⟩
  · intro v' hv' w' hw' hvw' hreach
    dsimp only [Prod.snd] at hreach
    rw [Finset.mem_erase] at hv' hw'
    have hsup : fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _) = fromEdgeSet (state.2 : Set _) ⊔ edge nextLeaf si := by
      ext a b; simp [fromEdgeSet, edge, Sym2.ToRel, Sym2.eq]; tauto
    rw [hsup] at hreach
    have h1 := reachable_sup_edge_graph hreach
    rcases h1 with (h2 | ⟨h3u, h3v⟩ | ⟨h4v, h4u⟩)
    · exact h_forest.uniq v' hv'.2 w' hw'.2 hvw' h2
    · have h_eq := h_forest.uniq v' hv'.2 nextLeaf hnL
      by_cases h_v' : v' = nextLeaf
      · exact hv'.1 h_v'
      · exact h_eq h_v' h3u
    · have h_eq := h_forest.uniq w' hw'.2 nextLeaf hnL
      by_cases h_w' : w' = nextLeaf
      · exact hw'.1 h_w'
      · exact h_eq h_w' h4u.symm


lemma nextLeaf_nonempty {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) (m : ℕ) (hm : m ≤ n - 2)
    (available : Finset (Fin n)) (h_card : available.card = n - m) :
    (available.filter (fun v => ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ v)).Nonempty := by
  let remaining_indices := Finset.univ.filter (fun j : Fin (n - 2) => m ≤ j.val)
  let img := remaining_indices.image s
  have h_rem_card : remaining_indices.card ≤ n - 2 - m := by
    have h_inj : Function.Injective (fun j : Fin (n - 2) => j.val) := Fin.val_injective
    have h_map : remaining_indices.image (fun j : Fin (n - 2) => j.val) ⊆ Finset.Ico m (n - 2) := by
      intro x hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨j, hj, rfl⟩
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_Ico]
      exact ⟨hj.2, j.isLt⟩
    calc
      remaining_indices.card = (remaining_indices.image (fun j => j.val)).card := (Finset.card_image_of_injective remaining_indices h_inj).symm
      _ ≤ (Finset.Ico m (n - 2)).card := Finset.card_le_card h_map
      _ = n - 2 - m := by rw [Nat.card_Ico]
  have h_img_card : img.card ≤ n - 2 - m := by
    calc
      img.card ≤ remaining_indices.card := Finset.card_image_le
      _ ≤ n - 2 - m := h_rem_card
  have h_intersect_card : (available ∩ img).card ≤ n - 2 - m := by
    calc
      (available ∩ img).card ≤ img.card := Finset.card_le_card Finset.inter_subset_right
      _ ≤ n - 2 - m := h_img_card
  have h_diff_card : 0 < (available \ img).card := by
    have h_add : (available \ img).card + (available ∩ img).card = available.card := Finset.card_sdiff_add_card_inter available img
    omega
  have h_nonempty : (available \ img).Nonempty := Finset.card_pos.mp h_diff_card
  rcases h_nonempty with ⟨v, hv⟩
  rw [Finset.mem_sdiff, Finset.mem_image] at hv
  refine ⟨v, Finset.mem_filter.mpr ⟨hv.1, ?_⟩⟩
  intro j hj heq
  exact hv.2 ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, heq⟩

def pruferDecodeAux {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    (m : ℕ) → (hm : m ≤ n - 2) →
    { state : Finset (Fin n) × Finset (Sym2 (Fin n)) //
      DecodeForestFull n state ∧ state.1.card = n - m ∧
      ∀ j : Fin (n - 2), m ≤ j.val → s j ∈ state.1 }
| 0, _ => ⟨(Finset.univ, ∅), by
    refine ⟨decodeForest_init n hn, by simp, ?_⟩
    intro j hj
    exact Finset.mem_univ _⟩
| m + 1, hm => by
    have h_m_le : m ≤ n - 2 := by omega
    let prev := pruferDecodeAux hn s m h_m_le
    let state := prev.val
    have h_forest := prev.property.1
    have h_card := prev.property.2.1
    have h_future := prev.property.2.2

    let si : Fin n := s ⟨m, by omega⟩
    have h_si_in : si ∈ state.1 := h_future ⟨m, by omega⟩ (by rfl)

    have h_nonempty := nextLeaf_nonempty hn s m h_m_le state.1 h_card
    let nextLeaf := (state.1.filter (fun v => ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ v)).min' h_nonempty
    have h_mem_filter : nextLeaf ∈ state.1.filter (fun v => ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ v) :=
      Finset.min'_mem _ _
    rw [Finset.mem_filter] at h_mem_filter
    have hnL : nextLeaf ∈ state.1 := h_mem_filter.1
    have h_not_in_future : ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ nextLeaf := h_mem_filter.2

    have h_not_eq : nextLeaf ≠ si := by
      have h := h_not_in_future ⟨m, by omega⟩ (by rfl)
      exact h.symm

    let new_state := (state.1.erase nextLeaf, insert s(nextLeaf, si) state.2)
    have h_new_forest := decodeForest_step h_forest nextLeaf hnL si h_si_in h_not_eq

    have h_new_card : new_state.1.card = n - (m + 1) := by
      dsimp [new_state]
      rw [Finset.card_erase_of_mem hnL]
      rw [h_card]
      omega

    have h_new_future : ∀ j : Fin (n - 2), m + 1 ≤ j.val → s j ∈ new_state.1 := by
      intro j hj
      dsimp [new_state]
      rw [Finset.mem_erase]
      have h_m_le_j : m ≤ j.val := by omega
      have h1 := h_future j h_m_le_j
      have h2 := h_not_in_future j h_m_le_j
      exact ⟨h2, h1⟩

    exact ⟨new_state, h_new_forest, h_new_card, h_new_future⟩


/-- The final-state pair `(available, edges)` after running the decode loop `n-2` times. -/
def pruferFinalState {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    Finset (Fin n) × Finset (Sym2 (Fin n)) :=
  (pruferDecodeAux hn s (n - 2) (by rfl)).val

lemma pruferFinalState_card {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    (pruferFinalState hn s).1.card = 2 := by
  have h : (pruferFinalState hn s).1.card = n - (n - 2) :=
    (pruferDecodeAux hn s (n - 2) (by rfl)).property.2.1
  omega

lemma pruferFinalState_forest {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    DecodeForestFull n (pruferFinalState hn s) :=
  (pruferDecodeAux hn s (n - 2) (by rfl)).property.1

lemma pruferFinalState_nonempty {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    (pruferFinalState hn s).1.Nonempty := by
  rw [← Finset.card_pos, pruferFinalState_card]; omega

/-- The smaller of the two remaining "active" vertices after the decode loop. -/
def pruferLastU {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) : Fin n :=
  (pruferFinalState hn s).1.min' (pruferFinalState_nonempty hn s)

lemma pruferLastU_mem {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    pruferLastU hn s ∈ (pruferFinalState hn s).1 := Finset.min'_mem _ _

lemma pruferFinalErase_card {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    ((pruferFinalState hn s).1.erase (pruferLastU hn s)).card = 1 := by
  rw [Finset.card_erase_of_mem (pruferLastU_mem hn s), pruferFinalState_card]

lemma pruferFinalErase_nonempty {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    ((pruferFinalState hn s).1.erase (pruferLastU hn s)).Nonempty := by
  rw [← Finset.card_pos, pruferFinalErase_card]; omega

/-- The larger of the two remaining "active" vertices. -/
def pruferLastV {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) : Fin n :=
  ((pruferFinalState hn s).1.erase (pruferLastU hn s)).min'
    (pruferFinalErase_nonempty hn s)

lemma pruferLastV_mem_erase {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    pruferLastV hn s ∈ (pruferFinalState hn s).1.erase (pruferLastU hn s) :=
  Finset.min'_mem _ _

lemma pruferLastV_mem {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    pruferLastV hn s ∈ (pruferFinalState hn s).1 :=
  Finset.mem_of_mem_erase (pruferLastV_mem_erase hn s)

lemma pruferLastU_ne_V {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    pruferLastU hn s ≠ pruferLastV hn s := by
  have := pruferLastV_mem_erase hn s
  rw [Finset.mem_erase] at this
  exact this.1.symm

def pruferDecodeEdges {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) : Finset (Sym2 (Fin n)) :=
  insert (s(pruferLastU hn s, pruferLastV hn s)) (pruferFinalState hn s).2

lemma pruferDecodeIsTree {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    (fromEdgeSet (V := Fin n) (pruferDecodeEdges hn s : Set (Sym2 (Fin n)))).IsTree := by
  unfold pruferDecodeEdges
  set state := pruferFinalState hn s with h_state_eq
  set u := pruferLastU hn s with h_u_eq
  set v := pruferLastV hn s with h_v_eq
  have h_forest : DecodeForestFull n state := pruferFinalState_forest hn s
  have h_card : state.1.card = 2 := pruferFinalState_card hn s
  have hu : u ∈ state.1 := pruferLastU_mem hn s
  have hv : v ∈ state.1 := pruferLastV_mem hn s
  have hv_mem2 : v ∈ state.1.erase u := pruferLastV_mem_erase hn s
  have h_card2 : (state.1.erase u).card = 1 := pruferFinalErase_card hn s
  have huv : u ≠ v := pruferLastU_ne_V hn s

  have hsup : fromEdgeSet (V := Fin n) (insert (s(u, v)) state.2 : Set (Sym2 (Fin n))) = fromEdgeSet (V := Fin n) (state.2 : Set (Sym2 (Fin n))) ⊔ edge u v := by
    ext a b; simp [fromEdgeSet, edge, Sym2.ToRel, Sym2.eq]; tauto

  have h_preconn : (fromEdgeSet (V := Fin n) (insert (s(u, v)) state.2 : Set (Sym2 (Fin n)))).Preconnected := by
    intro x y
    rcases h_forest.covers x with ⟨rx, hrx, hreach_x⟩
    rcases h_forest.covers y with ⟨ry, hry, hreach_y⟩

    have h_state1_eq : state.1 = {u, v} := by
      ext z
      rw [Finset.mem_insert, Finset.mem_singleton]
      refine ⟨fun hz => ?_, fun hz => ?_⟩
      · by_contra hc
        push Not at hc
        have hz_state2 : z ∈ (state.1.erase u) := Finset.mem_erase_of_ne_of_mem hc.1 hz
        have h_v_eq_z : v = z := by
          have h_sub : (state.1.erase u) ⊆ {v} := by
            intro a ha
            have h_eq : (state.1.erase u).card = 1 := h_card2
            rw [Finset.card_eq_one] at h_eq
            rcases h_eq with ⟨w, hw⟩
            have h_v_w : v ∈ ({w} : Finset (Fin n)) := by rw [← hw]; exact hv_mem2
            rw [Finset.mem_singleton] at h_v_w
            have h_a_w : a ∈ ({w} : Finset (Fin n)) := by rw [← hw]; exact ha
            rw [Finset.mem_singleton] at h_a_w
            rw [Finset.mem_singleton]
            exact h_a_w.trans h_v_w.symm
          have hz_in_v := h_sub hz_state2
          rw [Finset.mem_singleton] at hz_in_v
          exact hz_in_v.symm
        exact hc.2 h_v_eq_z.symm
      · rcases hz with rfl | rfl
        · exact hu
        · exact hv

    have hrx_eq : rx = u ∨ rx = v := by
      have hrx_in : rx ∈ ({u, v} : Finset (Fin n)) := by rw [← h_state1_eq]; exact hrx
      rw [Finset.mem_insert, Finset.mem_singleton] at hrx_in
      exact hrx_in

    have hry_eq : ry = u ∨ ry = v := by
      have hry_in : ry ∈ ({u, v} : Finset (Fin n)) := by rw [← h_state1_eq]; exact hry
      rw [Finset.mem_insert, Finset.mem_singleton] at hry_in
      exact hry_in

    have h_uv_reach : (fromEdgeSet (V := Fin n) (insert (s(u, v)) state.2 : Set (Sym2 (Fin n)))).Reachable u v := by
      rw [hsup]
      have h_edge : (fromEdgeSet (V := Fin n) (state.2 : Set (Sym2 (Fin n))) ⊔ edge u v).Adj u v := Or.inr ⟨by simp [Sym2.ToRel], huv⟩
      exact h_edge.reachable

    have hreach_x_new : (fromEdgeSet (V := Fin n) (insert (s(u, v)) state.2 : Set (Sym2 (Fin n)))).Reachable x rx := by
      rw [hsup]
      exact hreach_x.mono le_sup_left

    have hreach_y_new : (fromEdgeSet (V := Fin n) (insert (s(u, v)) state.2 : Set (Sym2 (Fin n)))).Reachable ry y := by
      rw [hsup]
      exact hreach_y.symm.mono le_sup_left

    have h_r_reach : (fromEdgeSet (V := Fin n) (insert (s(u, v)) state.2 : Set (Sym2 (Fin n)))).Reachable rx ry := by
      rcases hrx_eq with rfl | rfl
      · rcases hry_eq with rfl | rfl
        · exact Reachable.refl _
        · exact h_uv_reach
      · rcases hry_eq with rfl | rfl
        · exact h_uv_reach.symm
        · exact Reachable.refl _

    exact Reachable.trans hreach_x_new (Reachable.trans h_r_reach hreach_y_new)

  have h_acyclic : (fromEdgeSet (V := Fin n) (insert (s(u, v)) state.2 : Set (Sym2 (Fin n)))).IsAcyclic := by
    rw [hsup]
    rw [isAcyclic_sup_fromEdgeSet_iff]
    refine ⟨h_forest.acyclic, ?_⟩
    intro hreach
    exact False.elim (h_forest.uniq u hu v hv huv hreach)

  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rw [show (↑(insert s(u, v) state.2) : Set (Sym2 (Fin n))) = insert s(u, v) (↑state.2 : Set _)
      from Finset.coe_insert _ _]
  exact { connected := { preconnected := h_preconn }, isAcyclic := h_acyclic }

/-- The Prüfer decode wrapped as a `LabeledTree`. -/
def pruferDecode {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) : LabeledTree n :=
  ⟨fromEdgeSet (V := Fin n) (pruferDecodeEdges hn s : Set (Sym2 (Fin n))),
    pruferDecodeIsTree hn s⟩

/-- Iterative Prüfer encoding: indexed by `m`, where the tree has `m + 2` vertices.
At each step, record the neighbour of the smallest leaf, then recurse on the
tree with that leaf removed, lifting indices via `finSuccAboveEquivCompl`. -/
noncomputable def pruferEncodeAux : ∀ (m : ℕ), LabeledTree (m + 2) → Fin m → Fin (m + 2)
  | 0,   _ => Fin.elim0
  | m+1, T => fun i =>
    if h : i.val = 0 then
      smallestTreeLeafNeighbor (m + 3) (by omega) T
    else
      let leaf : Fin (m + 3) := smallestTreeLeaf (m + 3) (by omega) T
      let T' : LabeledTree (m + 2) := deleteSmallestLeafTreeSucc (m + 2) (by omega) T
      let i' : Fin m := ⟨i.val - 1, by omega⟩
      let inner : Fin (m + 2) := pruferEncodeAux m T' i'
      ((finSuccAboveEquivCompl leaf) inner).1

/-- Prüfer encoding of a labeled tree as a function `Fin (n - 2) → Fin n`. -/
noncomputable def pruferEncode : ∀ {n : ℕ}, 2 ≤ n → LabeledTree n → pruferCodeSpace n
  | 0,       hn, _ => absurd hn (by decide)
  | 1,       hn, _ => absurd hn (by decide)
  | (m + 2), _,  T => pruferEncodeAux m T







/-! Ch31 Tier 2: degree formula for the decoded forest. -/

 def countOccurrences {n : ℕ} (s : pruferCodeSpace n) (m : ℕ) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun (j : Fin (n - 2)) => j.val < m ∧ s j = v)).card

/-- Base case: at m = 0, no edges. -/
 theorem pruferDecodeAux_zero_degree (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (v : Fin n) (hm : 0 ≤ n - 2) :
    (fromEdgeSet (V := Fin n)
      ((pruferDecodeAux hn s 0 hm).val.2 : Set (Sym2 (Fin n)))).degree v = 0 := by
  unfold SimpleGraph.degree
  rw [Finset.card_eq_zero]
  ext x
  rw [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj]
  constructor
  · rintro ⟨hmem, _⟩
    have : (pruferDecodeAux hn s 0 hm).val.2 = ∅ := rfl
    rw [this] at hmem
    simp at hmem
  · intro h
    exact absurd h (by simp)

/-- Recursive structure: edge set at m+1 = insert one edge into edge set at m. -/
 lemma pruferDecodeAux_succ_val_2 {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (m : ℕ) (hm : m + 1 ≤ n - 2) :
    ∃ nextLeaf : Fin n,
      nextLeaf ∈ (pruferDecodeAux hn s m (by omega)).val.1 ∧
      (∀ j : Fin (n - 2), m ≤ j.val → s j ≠ nextLeaf) ∧
      (pruferDecodeAux hn s (m + 1) hm).val.2 =
        insert s(nextLeaf, s ⟨m, by omega⟩)
          (pruferDecodeAux hn s m (by omega)).val.2 ∧
      (pruferDecodeAux hn s (m + 1) hm).val.1 =
        (pruferDecodeAux hn s m (by omega)).val.1.erase nextLeaf := by
  set prev := pruferDecodeAux hn s m (by omega)
  set state := prev.val with hstate
  have h_card := prev.property.2.1
  have h_nonempty := nextLeaf_nonempty hn s m (by omega) state.1 h_card
  set nextLeaf := (state.1.filter (fun v => ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ v)).min' h_nonempty
    with hnextLeaf
  have h_mem_filter : nextLeaf ∈ state.1.filter (fun v => ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ v) :=
    Finset.min'_mem _ _
  rw [Finset.mem_filter] at h_mem_filter
  exact ⟨nextLeaf, h_mem_filter.1, h_mem_filter.2, rfl, rfl⟩





/-- Sym2 commutativity: `s(u, w) = s(w, u)` so the insert is symmetric. -/
 lemma sym2_pair_swap {V : Type*} (u w : V) : s(u, w) = s(w, u) :=
  Sym2.eq_swap

/-- Endpoint version usable when goal has `↑(insert e S : Finset _)` form. -/
 lemma fromEdgeSet_finset_insert_degree_endpoint {n : ℕ}
    (S : Finset (Sym2 (Fin n))) (u w : Fin n) (huw : u ≠ w)
    (h_not_in : s(u, w) ∉ S) :
    (fromEdgeSet (V := Fin n)
      (((insert s(u, w) S : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))))).degree u =
    (fromEdgeSet (V := Fin n) (S : Set (Sym2 (Fin n)))).degree u + 1 := by
  -- The base form is in Set.insert: lemma proven in that form.
  -- Use ext-based proof: unfold degree as neighborFinset.card, then case-split.
  unfold SimpleGraph.degree
  have h_w_not_neighbor :
      w ∉ (fromEdgeSet (V := Fin n) (S : Set (Sym2 (Fin n)))).neighborFinset u := by
    rw [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj]
    rintro ⟨hmem, _⟩
    exact h_not_in (by exact_mod_cast hmem)
  have h_eq : (fromEdgeSet (V := Fin n)
        (((insert s(u, w) S : Finset _) : Set _))).neighborFinset u =
      insert w ((fromEdgeSet (V := Fin n) (S : Set _)).neighborFinset u) := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj, Finset.coe_insert,
               Set.mem_insert_iff, Finset.mem_insert, Sym2.eq_iff]
    constructor
    · rintro ⟨hmem, hne⟩
      rcases hmem with hnew | hold
      · rcases hnew with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact absurd rfl hne
      · exact Or.inr ⟨hold, hne⟩
    · rintro (rfl | ⟨hmem, hne⟩)
      · refine ⟨Or.inl (Or.inl ?_), huw⟩
        tauto
      · exact ⟨Or.inr hmem, hne⟩
  rw [h_eq]
  exact Finset.card_insert_of_notMem h_w_not_neighbor

/-- Other version usable when goal has `↑(insert e S : Finset _)` form. -/
 lemma fromEdgeSet_finset_insert_degree_other {n : ℕ}
    (S : Finset (Sym2 (Fin n))) (u w v : Fin n) (huw : u ≠ w)
    (hv_u : v ≠ u) (hv_w : v ≠ w) :
    (fromEdgeSet (V := Fin n)
      (((insert s(u, w) S : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))))).degree v =
    (fromEdgeSet (V := Fin n) (S : Set (Sym2 (Fin n)))).degree v := by
  unfold SimpleGraph.degree
  congr 1
  ext x
  simp only [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj, Finset.coe_insert,
             Set.mem_insert_iff, Sym2.eq_iff]
  constructor
  · rintro ⟨hmem, hne⟩
    refine ⟨?_, hne⟩
    rcases hmem with ⟨heq | heq_swap⟩ | hinS
    · rcases heq with ⟨rfl, rfl⟩
      exact absurd rfl hv_u
    · rcases heq_swap with ⟨rfl, rfl⟩
      exact absurd rfl hv_w
    · exact hinS
  · rintro ⟨hmem, hne⟩
    exact ⟨Or.inr hmem, hne⟩

/-- countOccurrences recursion: stepping `m` to `m+1` adds 1 iff `s ⟨m, _⟩ = v`. -/
 lemma countOccurrences_succ {n : ℕ} (s : pruferCodeSpace n)
    (m : ℕ) (hm : m + 1 ≤ n - 2) (v : Fin n) :
    countOccurrences s (m + 1) v =
    countOccurrences s m v + (if s ⟨m, by omega⟩ = v then 1 else 0) := by
  unfold countOccurrences
  -- Filter at m+1 = filter at m ∪ (singleton ⟨m, _⟩ if s_m = v).
  rw [show (Finset.univ.filter (fun (j : Fin (n - 2)) => j.val < m + 1 ∧ s j = v)) =
       (Finset.univ.filter (fun (j : Fin (n - 2)) => j.val < m ∧ s j = v)) ∪
       (Finset.univ.filter (fun (j : Fin (n - 2)) => j.val = m ∧ s j = v)) from ?_]
  · rw [Finset.card_union_of_disjoint]
    · congr 1
      by_cases hsm : s ⟨m, by omega⟩ = v
      · simp [hsm]
        rw [show (Finset.univ.filter (fun (j : Fin (n - 2)) => j.val = m ∧ s j = v)) =
             {⟨m, by omega⟩} from ?_]
        · simp
        · ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨hval, _⟩
            ext
            exact hval
          · rintro rfl
            exact ⟨rfl, hsm⟩
      · simp [hsm]
        intro x hval hsx
        apply hsm
        have : x = ⟨m, by omega⟩ := by ext; exact hval
        rw [← hsx, this]
    · rw [Finset.disjoint_filter]
      intros j _ h1 h2
      omega
  · ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hval, hs⟩
      by_cases h : j.val = m
      · exact Or.inr ⟨h, hs⟩
      · exact Or.inl ⟨by omega, hs⟩
    · rintro (⟨h, hs⟩ | ⟨h, hs⟩)
      · exact ⟨by omega, hs⟩
      · exact ⟨by omega, hs⟩

/-- Degree formula: after m iterations of `pruferDecodeAux`, the degree of
vertex v in the constructed graph equals the number of times v appears as
`s j` for `j.val < m`, plus 1 if v has already been "popped" (i.e., v has
been chosen as a `nextLeaf` and erased from the available set). -/
 theorem pruferDecodeAux_degree (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    ∀ (m : ℕ) (hm : m ≤ n - 2) (v : Fin n),
    (fromEdgeSet (V := Fin n)
      ((pruferDecodeAux hn s m hm).val.2 : Set (Sym2 (Fin n)))).degree v =
    countOccurrences s m v +
    (if v ∈ (pruferDecodeAux hn s m hm).val.1 then 0 else 1) := by
  intro m
  induction m with
  | zero =>
    intro hm v
    rw [pruferDecodeAux_zero_degree n hn s v hm]
    have hcount : countOccurrences s 0 v = 0 := by
      apply Finset.card_eq_zero.mpr
      ext j; simp
    have hmem : v ∈ (pruferDecodeAux hn s 0 hm).val.1 := by
      show v ∈ Finset.univ; exact Finset.mem_univ v
    rw [hcount, if_pos hmem]
  | succ m ih =>
    intro hm v
    -- Sub-key facts about transitions from step m to m+1.
    have h_m_le : m ≤ n - 2 := by omega
    obtain ⟨nextLeaf, hnL_mem, hnL_filter, h_edges_eq, h_avail_eq⟩ :=
      pruferDecodeAux_succ_val_2 hn s m hm
    -- The m-th code entry.
    set si : Fin n := s ⟨m, by omega⟩ with hsi_def
    -- nextLeaf ≠ si: from filter property at j = ⟨m, _⟩.
    have h_nL_ne_si : nextLeaf ≠ si := by
      have := hnL_filter ⟨m, by omega⟩ (by rfl)
      exact (this.symm)
    -- si is in available set at step m (from h_future invariant).
    have h_si_in_prev : si ∈ (pruferDecodeAux hn s m h_m_le).val.1 := by
      have h_future := (pruferDecodeAux hn s m h_m_le).property.2.2
      exact h_future ⟨m, by omega⟩ (by rfl)
    -- Edge s(nextLeaf, si) not already in state.2:
    -- Proof: if it were, then since fromEdgeSet (state.2) is a forest, and
    -- nextLeaf, si are connected in fromEdgeSet (state.2), they're in different
    -- trees. But h_si_in_prev and hnL_mem say both in state.1, and the forest
    -- has each state.1 vertex as a distinct tree root → they aren't reachable
    -- to each other (uniq property).
    have h_edge_not_in : s(nextLeaf, si) ∉ (pruferDecodeAux hn s m h_m_le).val.2 := by
      intro hmem
      have h_forest := (pruferDecodeAux hn s m h_m_le).property.1
      have h_adj : (fromEdgeSet (V := Fin n)
        ((pruferDecodeAux hn s m h_m_le).val.2 : Set (Sym2 (Fin n)))).Adj nextLeaf si := by
        rw [fromEdgeSet_adj]
        exact ⟨by exact_mod_cast hmem, h_nL_ne_si⟩
      have h_reach := h_adj.reachable
      have h_uniq := h_forest.uniq
      exact h_uniq nextLeaf hnL_mem si h_si_in_prev h_nL_ne_si h_reach
    -- Now case on v's relation to nextLeaf and si.
    -- Rewrite goal's val.2 and val.1 via the recursion equations.
    -- Both sides reduce to expressions in `(pruferDecodeAux hn s m h_m_le).val.{1,2}`.
    have h_lhs_eq : (fromEdgeSet (V := Fin n)
        ((pruferDecodeAux hn s (m+1) hm).val.2 : Set (Sym2 (Fin n)))).degree v =
      (fromEdgeSet (V := Fin n)
        ((insert s(nextLeaf, si) (pruferDecodeAux hn s m h_m_le).val.2 :
            Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))).degree v := by
      rw [h_edges_eq]
    have h_indicator_eq :
        (if v ∈ (pruferDecodeAux hn s (m+1) hm).val.1 then (0:ℕ) else 1) =
        (if v ∈ (pruferDecodeAux hn s m h_m_le).val.1.erase nextLeaf
          then (0:ℕ) else 1) := by
      rw [h_avail_eq]
    rw [h_lhs_eq, h_indicator_eq]
    rw [countOccurrences_succ s m hm v]
    have ih_m := ih h_m_le v
    by_cases hv_nL : v = nextLeaf
    · -- Case 1: v = nextLeaf. Substitute v throughout.
      subst hv_nL
      rw [fromEdgeSet_finset_insert_degree_endpoint
        (pruferDecodeAux hn s m h_m_le).val.2 v si h_nL_ne_si h_edge_not_in]
      rw [ih_m, if_pos hnL_mem]
      have hsm_ne : ¬ s ⟨m, by omega⟩ = v := h_nL_ne_si.symm
      simp [hsm_ne]
    · by_cases hv_si : v = si
      · -- Case 2: v = si.
        rw [hv_si]  -- Goal now has si everywhere instead of v.
        have h_edge_swap : s(nextLeaf, si) = s(si, nextLeaf) := sym2_pair_swap _ _
        rw [h_edge_swap]
        have h_edge_not_in' : s(si, nextLeaf) ∉ (pruferDecodeAux hn s m h_m_le).val.2 := by
          rw [← h_edge_swap]; exact h_edge_not_in
        have h_si_ne_nL : si ≠ nextLeaf := h_nL_ne_si.symm
        rw [fromEdgeSet_finset_insert_degree_endpoint
          (pruferDecodeAux hn s m h_m_le).val.2 si nextLeaf h_si_ne_nL h_edge_not_in']
        rw [hv_si] at ih_m
        rw [ih_m, if_pos h_si_in_prev]
        have hsm_eq : s ⟨m, by omega⟩ = si := rfl
        rw [if_pos hsm_eq]
        have hsi_in_erase : si ∈ (pruferDecodeAux hn s m h_m_le).val.1.erase nextLeaf := by
          rw [Finset.mem_erase]
          exact ⟨h_si_ne_nL, h_si_in_prev⟩
        rw [if_pos hsi_in_erase]
      · -- Case 3: v ≠ nextLeaf and v ≠ si.
        rw [fromEdgeSet_finset_insert_degree_other
          (pruferDecodeAux hn s m h_m_le).val.2 nextLeaf si v h_nL_ne_si hv_nL hv_si]
        rw [ih_m]
        have hsm_ne : ¬ s ⟨m, by omega⟩ = v := fun h => hv_si (h.symm)
        rw [if_neg hsm_ne]
        have h_erase_iff :
            (v ∈ (pruferDecodeAux hn s m h_m_le).val.1.erase nextLeaf) ↔
            (v ∈ (pruferDecodeAux hn s m h_m_le).val.1) := by
          rw [Finset.mem_erase]
          exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv_nL, h⟩⟩
        by_cases h : v ∈ (pruferDecodeAux hn s m h_m_le).val.1
        · rw [if_pos h, if_pos (h_erase_iff.mpr h)]
        · rw [if_neg h, if_neg (fun hh => h (h_erase_iff.mp hh))]

/-- pruferFinalState.1 = {pruferLastU, pruferLastV}. -/
 lemma pruferFinalState_1_eq_pair (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 = {pruferLastU hn s, pruferLastV hn s} := by
  have h_uv_ne : pruferLastU hn s ≠ pruferLastV hn s := pruferLastU_ne_V hn s
  have h_u_mem : pruferLastU hn s ∈ (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := pruferLastU_mem hn s
  have h_v_mem : pruferLastV hn s ∈ (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := pruferLastV_mem hn s
  have h_card : (pruferDecodeAux hn s (n - 2) (by rfl)).val.1.card = 2 := pruferFinalState_card hn s
  have h_sub : ({pruferLastU hn s, pruferLastV hn s} : Finset (Fin n)) ⊆
               (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h_u_mem
    · exact h_v_mem
  have h_pair_card : ({pruferLastU hn s, pruferLastV hn s} : Finset (Fin n)).card = 2 :=
    Finset.card_pair h_uv_ne
  exact (Finset.eq_of_subset_of_card_le h_sub (by omega)).symm

/-- The famous Prüfer degree formula: in the decoded tree, every vertex's
degree equals `1 + (# times v appears in the code)`. -/
theorem pruferDecode_degree (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (v : Fin n) :
    ((pruferDecode hn s).1).degree v = countOccurrences s (n - 2) v + 1 := by
  -- pruferDecode = ⟨fromEdgeSet (pruferDecodeEdges hn s : Set _), _⟩.
  -- Both LHS and RHS interpret degree via SimpleGraph.degree; the underlying
  -- graphs are defeq but Fintype instances differ. Use Nat.card via neighborSet.
  have h_card_eq : ((pruferDecode hn s).1).degree v =
      (fromEdgeSet (V := Fin n)
        (pruferDecodeEdges hn s : Set (Sym2 (Fin n)))).degree v := by
    -- Both degrees equal Nat.card (neighborSet v), independent of Fintype instance.
    have h1 : ((pruferDecode hn s).1).degree v =
              (((pruferDecode hn s).1).neighborFinset v).card := rfl
    have h2 : (fromEdgeSet (V := Fin n)
        (pruferDecodeEdges hn s : Set (Sym2 (Fin n)))).degree v =
              ((fromEdgeSet (V := Fin n)
        (pruferDecodeEdges hn s : Set (Sym2 (Fin n)))).neighborFinset v).card := rfl
    rw [h1, h2]
    -- Both neighborFinsets contain the same elements (Adj is the same).
    congr 1
    ext x
    simp [SimpleGraph.mem_neighborFinset]
    rfl
  rw [h_card_eq]
  unfold pruferDecodeEdges
  set u := pruferLastU hn s with hu_def
  set w := pruferLastV hn s with hw_def
  -- pruferDecodeEdges = insert s(u, w) (pruferDecodeAux hn s (n - 2) (by rfl)).val.2.
  have h_uw_ne : u ≠ w := pruferLastU_ne_V hn s
  -- Unfold pruferFinalState to match pruferDecodeAux_degree's signature.
  show (fromEdgeSet (V := Fin n)
        ((insert s(u, w) (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 :
            Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))).degree v =
        countOccurrences s (n - 2) v + 1
  -- Step 2: edge s(u, w) not in pruferFinalState.2 (forest invariant).
  have h_edge_not_in : s(u, w) ∉ (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 := by
    intro hmem
    have h_forest := (pruferDecodeAux hn s (n - 2) (by rfl)).property.1
    have h_adj : (fromEdgeSet (V := Fin n)
      ((pruferDecodeAux hn s (n - 2) (by rfl)).val.2 : Set (Sym2 (Fin n)))).Adj u w := by
      rw [fromEdgeSet_adj]
      exact ⟨by exact_mod_cast hmem, h_uw_ne⟩
    exact h_forest.uniq u (pruferLastU_mem hn s) w (pruferLastV_mem hn s)
      h_uw_ne h_adj.reachable
  -- Step 3: case split on whether v = u or v = w or neither.
  by_cases hv_u : v = u
  · -- After subst, v ↦ u; use u throughout.
    subst hv_u
    rw [fromEdgeSet_finset_insert_degree_endpoint
      (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 u w h_uw_ne h_edge_not_in]
    rw [pruferDecodeAux_degree n hn s (n - 2) (by rfl) u]
    have h_u_mem : u ∈ (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := pruferLastU_mem hn s
    rw [if_pos h_u_mem]
  · by_cases hv_w : v = w
    · subst hv_w
      have h_swap : s(u, w) = s(w, u) := sym2_pair_swap _ _
      rw [h_swap]
      have h_edge_not_in' : s(w, u) ∉ (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 := by
        rw [← h_swap]; exact h_edge_not_in
      have h_w_ne_u : w ≠ u := hv_u
      rw [fromEdgeSet_finset_insert_degree_endpoint
        (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 w u h_w_ne_u h_edge_not_in']
      rw [pruferDecodeAux_degree n hn s (n - 2) (by rfl) w]
      have h_w_mem : w ∈ (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := pruferLastV_mem hn s
      rw [if_pos h_w_mem]
    · rw [fromEdgeSet_finset_insert_degree_other
        (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 u w v h_uw_ne hv_u hv_w]
      rw [pruferDecodeAux_degree n hn s (n - 2) (by rfl) v]
      have h_v_notin : v ∉ (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := by
        rw [pruferFinalState_1_eq_pair]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hv_u, hv_w⟩
      rw [if_neg h_v_notin]

lemma degree_eq_one_iff_exists_unique_adj {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n} :
    G.degree v = 1 ↔ ∃! w, G.Adj v w := by
  have h_deg : G.degree v = (G.neighborFinset v).card := rfl
  rw [h_deg, Finset.card_eq_one]
  constructor
  · rintro ⟨w, hw⟩
    use w
    have h_mem : w ∈ G.neighborFinset v := by rw [hw]; exact Finset.mem_singleton_self w
    simp only [SimpleGraph.mem_neighborFinset] at h_mem
    refine ⟨h_mem, ?_⟩
    intro y hy
    have h_mem_y : y ∈ G.neighborFinset v := by simp only [SimpleGraph.mem_neighborFinset, hy]
    rw [hw, Finset.mem_singleton] at h_mem_y
    exact h_mem_y
  · rintro ⟨w, hw1, hw2⟩
    use w
    ext x
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · intro hx
      exact hw2 x hx
    · rintro rfl
      exact hw1

/-- A vertex is a tree-leaf in the decoded tree iff it doesn't appear in the code. -/
theorem pruferDecode_isLeaf_iff (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (v : Fin n) :
    v ∈ treeLeaves (pruferDecode hn s) ↔ isLeafInPrufer s v := by
  have h_leaf : v ∈ treeLeaves (pruferDecode hn s) ↔ ((pruferDecode hn s).1).degree v = 1 := by
    unfold treeLeaves
    classical
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact degree_eq_one_iff_exists_unique_adj.symm
  rw [h_leaf]
  rw [pruferDecode_degree n hn s v]
  have h_eq : countOccurrences s (n - 2) v + 1 = 1 ↔ countOccurrences s (n - 2) v = 0 := by omega
  rw [h_eq]
  unfold countOccurrences
  rw [Finset.card_eq_zero]
  constructor
  · intro h i
    have hi : i ∉ Finset.univ.filter (fun (j : Fin (n - 2)) => j.val < n - 2 ∧ s j = v) := by
      rw [h]
      simp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hi
    exact hi i.isLt
  · intro h
    ext i
    simp [h i]











/-- nextLeaf_0: the smallest tree-leaf of the decoded tree (= smallest Prüfer-leaf). -/
noncomputable def nextLeaf0 {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) : Fin n :=
  smallestTreeLeaf n hn (pruferDecode hn s)

/-- nextLeaf_0 doesn't appear in s anywhere. Immediate from pruferDecode_isLeaf_iff. -/
theorem nextLeaf0_not_in_image {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    ∀ j : Fin (n - 2), s j ≠ nextLeaf0 hn s := by
  have h_leaf : nextLeaf0 hn s ∈ treeLeaves (pruferDecode hn s) :=
    smallestTreeLeaf_mem_leaves n hn (pruferDecode hn s)
  rw [pruferDecode_isLeaf_iff n hn s] at h_leaf
  exact h_leaf

/-- The shifted code: drop position 0, lift values through `(finSuccAboveEquivCompl nextLeaf0).symm`. -/
noncomputable def shiftedCode_v2 {m : ℕ} (hm : 1 ≤ m) (s : pruferCodeSpace (m + 2)) :
    pruferCodeSpace (m + 1) := by
  intro j'
  classical
  have h2le : 2 ≤ m + 2 := by omega
  let nL : Fin (m + 2) := nextLeaf0 h2le s
  have hj_lt : j'.val + 1 < (m + 2) - 2 := by have := j'.isLt; omega
  let j : Fin ((m + 2) - 2) := ⟨j'.val + 1, hj_lt⟩
  have hNe : s j ≠ nL := nextLeaf0_not_in_image h2le s j
  have hMem : (s j : Fin (m + 2)) ∈ ({nL}ᶜ : Set (Fin (m + 2))) := by simp [hNe]
  let lifted : {v : Fin (m + 2) // v ∈ ({nL}ᶜ : Set (Fin (m + 2)))} := ⟨s j, hMem⟩
  exact (finSuccAboveEquivCompl nL).symm lifted



























-- Tier 1.5: take the structural correspondence as hypothesis.





end ProofsInTheBook.Chapter31


