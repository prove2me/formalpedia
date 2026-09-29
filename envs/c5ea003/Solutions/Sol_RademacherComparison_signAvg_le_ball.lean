-- Prove2me | solution 1 for RademacherComparison.signAvg_le_ball
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:56:32.475856+00:00
-- url     : https://prove2.me/submissions/e3acc00e-e818-4b17-856d-e65bb7653b29

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


lemma sgn_sq (ε : Fin n → Bool) (i : Fin n) : (sgn ε i) ^ 2 = 1 := by
  simp only [sgn]
  rcases Bool.eq_false_or_eq_true (ε i) with h | h <;> simp [h]











open RademacherComparison in
theorem solution{r : ℝ} (hr : 0 ≤ r) (hn : 0 < n) {v : Fin n → ℝ}
    (hv : v ∈ ball n r) (ε : Fin n → Bool) : signAvg ε v ≤ r / Real.sqrt n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hcs : (∑ i, sgn ε i * v i) ^ 2 ≤ ((n:ℝ)) * r ^ 2 := by
    have h := sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) (sgn ε) v
    have hone : ∑ i, (sgn ε i) ^ 2 = (n:ℝ) := by simp [sgn_sq]
    calc (∑ i, sgn ε i * v i) ^ 2 ≤ (∑ i, (sgn ε i) ^ 2) * (∑ i, (v i) ^ 2) := h
      _ = (n:ℝ) * (∑ i, (v i) ^ 2) := by rw [hone]
      _ ≤ (n:ℝ) * r ^ 2 := by
          have : ∑ i, (v i) ^ 2 ≤ r ^ 2 := hv
          nlinarith
  have hsqrt : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have hns : Real.sqrt n * Real.sqrt n = (n:ℝ) := Real.mul_self_sqrt hn'.le
  have hle : ∑ i, sgn ε i * v i ≤ Real.sqrt n * r := by
    by_contra hcon
    push_neg at hcon
    have h0 : 0 ≤ Real.sqrt n * r := mul_nonneg hsqrt.le hr
    have hsq : (Real.sqrt n * r) ^ 2 < (∑ i, sgn ε i * v i) ^ 2 := by nlinarith
    have heq : (Real.sqrt n * r) ^ 2 = (n:ℝ) * r ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hn'.le]
    linarith [hcs, hsq, heq.symm.le, heq.le]
  have hfin : (1 / (n:ℝ)) * (Real.sqrt n * r) = r / Real.sqrt n := by
    field_simp
    nlinarith [hns]
  unfold signAvg
  calc (1 / (n:ℝ)) * ∑ i, sgn ε i * v i ≤ (1 / (n:ℝ)) * (Real.sqrt n * r) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = r / Real.sqrt n := hfin
