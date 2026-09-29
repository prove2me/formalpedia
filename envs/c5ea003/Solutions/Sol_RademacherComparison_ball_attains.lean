-- Prove2me | solution 1 for RademacherComparison.ball_attains
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:56:31.220809+00:00
-- url     : https://prove2.me/submissions/08353151-17f4-465a-92fc-cde1ca0855fb

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
theorem solution{r : ℝ} (hn : 0 < n) (ε : Fin n → Bool) :
    (fun i => r / Real.sqrt n * sgn ε i) ∈ ball n r ∧
      signAvg ε (fun i => r / Real.sqrt n * sgn ε i) = r / Real.sqrt n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hsqrt : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have hns : Real.sqrt n * Real.sqrt n = (n:ℝ) := Real.mul_self_sqrt hn'.le
  constructor
  · show ∑ i, (r / Real.sqrt n * sgn ε i) ^ 2 ≤ r ^ 2
    have hsq2 : ∀ i : Fin n, (r / Real.sqrt n * sgn ε i) ^ 2 = r ^ 2 / (n:ℝ) := by
      intro i
      rw [mul_pow, sgn_sq, mul_one, div_pow, Real.sq_sqrt hn'.le]
    have hcalc : (n:ℝ) * (r ^ 2 / (n:ℝ)) = r ^ 2 := by field_simp
    rw [Finset.sum_congr rfl fun i _ => hsq2 i, Finset.sum_const, nsmul_eq_mul]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [hcalc]
  · unfold signAvg
    have hpt : ∀ i : Fin n, sgn ε i * (r / Real.sqrt n * sgn ε i) = r / Real.sqrt n := by
      intro i
      calc sgn ε i * (r / Real.sqrt n * sgn ε i) = (r / Real.sqrt n) * (sgn ε i) ^ 2 := by
            ring
        _ = r / Real.sqrt n := by rw [sgn_sq, mul_one]
    rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_const, nsmul_eq_mul]
    simp only [Finset.card_univ, Fintype.card_fin]
    field_simp
