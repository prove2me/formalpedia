-- Prove2me | solution 1 for RademacherComparison.ball_infinite
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:56:31.71984+00:00
-- url     : https://prove2.me/submissions/91089606-4e14-4bbf-b093-5fea9d6976b6

-- Sol generated from Logic/Rademacher/Comparison.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Comparison
/-
# Rademacher complexity beats cardinality (VC) counting on structured classes

Massart's finite class lemma bounds the Rademacher complexity of a class of `N` vectors
by `r √(2 log N)/n`, and VC-type bounds bound `N` (the number of behaviours on the
sample) by a function of the VC dimension.  Both are *counting* bounds and become
vacuous for classes that are infinite on the sample.

This file computes the empirical Rademacher complexity of the Euclidean ball of
radius `r`, i.e. of the class of all vectors of length at most `r`:

  `rad (ball r) = r / √n`   (`rad_ball`),

and shows that this class is infinite (`ball_infinite`), so no cardinality bound
applies to it, while its Rademacher complexity is finite, dimension free, and even
*exactly* computable.  Every subclass of the ball inherits the bound
(`rad_le_of_subset_ball`), which is the abstract form of the margin bound for linear
predictors.

Finally `vc_bound_eventually_worse` records the quantitative comparison: for a class of
linear predictors in dimension `d`, the VC dimension grows with `d`, so any bound of the
shape `c √(d/n)` eventually exceeds the dimension-free Rademacher bound `W B / √n`.

This file is self-contained.
-/

open RademacherComparison

open Finset

variable {n : ℕ}













open RademacherComparison in
theorem solution{r : ℝ} (hr : 0 < r) (hn : 0 < n) : (ball n r).Infinite := by
  have hi : Set.InjOn (fun t : ℝ => (fun i : Fin n => if i = ⟨0, hn⟩ then t else 0))
      (Set.Icc 0 r) := by
    intro a _ b _ hab
    have := congrFun hab ⟨0, hn⟩
    simpa using this
  have hsub : (fun t : ℝ => (fun i : Fin n => if i = ⟨0, hn⟩ then t else 0)) ''
      (Set.Icc 0 r) ⊆ ball n r := by
    rintro v ⟨t, ht, rfl⟩
    show ∑ i, (if i = (⟨0, hn⟩ : Fin n) then t else 0) ^ 2 ≤ r ^ 2
    have : ∑ i : Fin n, (if i = (⟨0, hn⟩ : Fin n) then t else 0) ^ 2 = t ^ 2 := by
      rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; simp at h
    rw [this]
    obtain ⟨h0, h1⟩ := ht
    nlinarith
  exact Set.Infinite.mono hsub (((Set.Icc_infinite hr).image hi))
