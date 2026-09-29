-- Prove2me | solution 1 for GracefulTrees.edgePartition_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:29:40.697312+00:00
-- url     : https://prove2.me/submissions/0416871d-82f9-4448-8b9a-540c3c5f2c13

-- Sol generated from Algebra/GracefulTrees.lean
import Mathlib
import Definitions.Def_Algebra_GracefulTrees

/-!
# Graceful labelings of paths and their decomposition connection

The Graceful Tree Conjecture is open.  This file formalizes the standard notion and proves
an infinite established case: every finite path is graceful.  It also proves the elementary
counting theorem used when graceful copies partition the edges of a complete graph.
-/

open Finset SimpleGraph

open GracefulTrees












open GracefulTrees in
theorem solution{W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) [Fintype K.edgeSet] (ι : Type*) [Fintype ι]
    (pieces : ι → Finset (Sym2 W)) (m : ℕ)
    (hpart : EdgePartition K ι pieces) (hcard : ∀ i, (pieces i).card = m) :
    K.edgeFinset.card = Fintype.card ι * m := by
  classical
  have hunion : Finset.univ.biUnion pieces = K.edgeFinset := by
    ext e
    constructor
    · intro he
      rw [Finset.mem_biUnion] at he
      obtain ⟨i, _, hei⟩ := he
      exact hpart.1 i hei
    · intro he
      obtain ⟨i, hei, _⟩ := hpart.2 e he
      rw [Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ _, hei⟩
  have hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint pieces := by
    intro i _ j _ hij
    change Disjoint (pieces i) (pieces j)
    rw [Finset.disjoint_left]
    intro e hei hej
    obtain ⟨k, hk, huniq⟩ := hpart.2 e (hpart.1 i hei)
    exact hij ((huniq i hei).trans (huniq j hej).symm)
  have hsum : K.edgeFinset.card = ∑ i, (pieces i).card := by
    rw [← hunion, Finset.card_biUnion hdisj]
  rw [hsum]
  simp [hcard]
