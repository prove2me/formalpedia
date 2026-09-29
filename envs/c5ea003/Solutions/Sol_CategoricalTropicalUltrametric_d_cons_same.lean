-- Prove2me | solution 1 for CategoricalTropicalUltrametric.d_cons_same
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:05:56.980086+00:00
-- url     : https://prove2.me/submissions/37de7d37-7024-4d68-83c7-39d3c82dc75e

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


/-- Below `firstDiff x y` the two addresses agree. -/
theorem firstDiff_min {x y : Addr} {i : ℕ} (hi : i < firstDiff x y) : x i = y i := by
  by_contra hc
  exact absurd (Nat.sInf_le (show i ∈ {n | x n ≠ y n} from hc)) (not_le.mpr hi)









/-- The value of `d` on a pair of addresses that first differ at index `n`. -/
theorem d_eq_of_firstDiff {x y : Addr} {n : ℕ} (hn : x n ≠ y n) (hlt : ∀ i < n, x i = y i) :
    d x y = (1 / 2 : ℝ) ^ n := by
  have hne : x ≠ y := fun h => hn (by rw [h])
  rw [d, if_neg hne, firstDiff_eq_of x y n hn hlt]






theorem cons_injective (k : Fin 3) {x y : Addr} (h : cons k x = cons k y) : x = y := by
  refine Addr.ext fun n => ?_
  have := congrFun h (n + 1)
  simpa using this





open CategoricalTropicalUltrametric in
theorem solution(k : Fin 3) (x y : Addr) :
    d (cons k x) (cons k y) = (1 / 2 : ℝ) * d x y := by
  by_cases hxy : x = y
  · simp [hxy, d_self]
  · have hne : cons k x ≠ cons k y := fun h => hxy (cons_injective k h)
    set n := firstDiff x y with hn
    have hdiff : x n ≠ y n := firstDiff_spec hxy
    have h1 : cons k x (n + 1) ≠ cons k y (n + 1) := by simpa using hdiff
    have h2 : ∀ i < n + 1, cons k x i = cons k y i := by
      intro i hi
      match i with
      | 0 => rfl
      | j + 1 => simpa using firstDiff_min (x := x) (y := y) (i := j) (by omega)
    rw [d_eq_of_firstDiff h1 h2, d, if_neg hxy, ← hn]
    ring
