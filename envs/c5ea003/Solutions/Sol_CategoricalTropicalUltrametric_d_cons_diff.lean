-- Prove2me | solution 1 for CategoricalTropicalUltrametric.d_cons_diff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:05:56.470787+00:00
-- url     : https://prove2.me/submissions/2615576b-2c48-43d0-83ba-867a4067c7f5

-- Sol generated from Bridges/BerggrenTrees/BerggrenBoundaryUltrametric.lean
import Mathlib
import Definitions.Def_Bridges_BerggrenTrees_BerggrenBoundaryUltrametric
/-
  # The Berggren Boundary Ultrametric (Conjecture C1, analytic half)

  The ternary Berggren tree of primitive Pythagorean triples is a rooted `3`-ary tree:
  every primitive triple has exactly three children `A`, `B`, `C`.  An infinite descent
  through the tree is therefore an *address* `x : ℕ → Fin 3`, and the set of all such
  addresses is the boundary `Addr` of the tree.

  This file supplies the bespoke tree ultrametric

  `d x y = 2 ^ (-firstDiff x y)`,  `firstDiff x y = min { n | x n ≠ y n }`,

  together with all the axioms needed to package it as a Mathlib `MetricSpace` and
  `IsUltrametricDist` (which is done in `FunctorialTropicalPythagoreanMetric.lean`):
  `d_self`, `d_comm`, `d_nonneg`, `d_eq_zero_iff`, `d_ultra`, `d_triangle`, `d_le_one`,
  and the two branch lemmas `d_cons_same` (each branch insertion is an exact `1/2`
  similarity) and `d_cons_diff` (distinct branches are maximally separated).

  -- !-- Lab Notes -- !--
  HYPOTHESIS: the "first place where two descents through the Berggren tree diverge"
  is a genuine ultrametric, and branch insertion `cons k` scales it by exactly `1/2`.
  EXPERIMENT: define `firstDiff` as `sInf {n | x n ≠ y n}` and characterise it by the
  pair (`differs at n`, `agrees below n`); everything else follows from that lemma.
  ANALYSIS: the strong triangle inequality needs no induction — at the first index
  where `x` and `z` differ, one of `x, y` or `y, z` must already differ, so one of the
  two distances is at least `d x z`.
  CRITIQUE: `firstDiff x x = 0` by the `sInf ∅ = 0` convention, so `d` must be defined
  by a case split on `x = y`; every lemma below is stated for the case-split version.
-/

open CategoricalTropicalUltrametric

open Classical





/-- The characterising property of `firstDiff`. -/
theorem firstDiff_eq_of (x y : Addr) (n : ℕ) (hn : x n ≠ y n) (hlt : ∀ i < n, x i = y i) :
    firstDiff x y = n := by
  refine le_antisymm (Nat.sInf_le hn) (le_of_not_gt fun hgt => ?_)
  have hmem : firstDiff x y ∈ {n | x n ≠ y n} := Nat.sInf_mem ⟨n, hn⟩
  exact hmem (hlt _ hgt)











/-- The value of `d` on a pair of addresses that first differ at index `n`. -/
theorem d_eq_of_firstDiff {x y : Addr} {n : ℕ} (hn : x n ≠ y n) (hlt : ∀ i < n, x i = y i) :
    d x y = (1 / 2 : ℝ) ^ n := by
  have hne : x ≠ y := fun h => hn (by rw [h])
  rw [d, if_neg hne, firstDiff_eq_of x y n hn hlt]











open CategoricalTropicalUltrametric in
theorem solution{k k' : Fin 3} (hk : k ≠ k') (x y : Addr) :
    d (cons k x) (cons k' y) = 1 := by
  have h1 : cons k x 0 ≠ cons k' y 0 := by simpa using hk
  have := d_eq_of_firstDiff h1 (by omega)
  simpa using this
