-- Prove2me | solution 1 for RademacherComparison.rad_le_of_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:01:22.088402+00:00
-- url     : https://prove2.me/submissions/85abdac3-4938-4a58-bd9a-42ed4bef168a

-- Sol generated from Logic/Rademacher/Comparison.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Comparison
import Theorems.Thm_RademacherComparison_signAvg_le_ball
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
theorem solution{F : Set (Fin n → ℝ)} {r : ℝ} (hr : 0 ≤ r) (hn : 0 < n)
    (hF : F ⊆ ball n r) : rad F ≤ r / Real.sqrt n := by
  have hpow : (0:ℝ) < 2 ^ n := by positivity
  have hsup : ∀ ε : Fin n → Bool, sSup (signAvg ε '' F) ≤ r / Real.sqrt n := by
    intro ε
    refine Real.sSup_le ?_ (by positivity)
    rintro a ⟨v, hv, rfl⟩
    exact signAvg_le_ball hr hn (hF hv) ε
  unfold rad
  rw [div_le_iff₀ hpow]
  calc ∑ ε : Fin n → Bool, sSup (signAvg ε '' F)
      ≤ ∑ _ε : Fin n → Bool, r / Real.sqrt n := Finset.sum_le_sum fun ε _ => hsup ε
    _ = r / Real.sqrt n * 2 ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        push_cast
        ring
