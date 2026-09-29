-- Prove2me | solution 1 for RademacherComparison.rad_ball
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:01:21.42307+00:00
-- url     : https://prove2.me/submissions/a007c1d8-1ecb-49c7-a97a-da97acc7abb4

-- Sol generated from Logic/Rademacher/Comparison.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Comparison
import Theorems.Thm_RademacherComparison_ball_attains
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
theorem solution{r : ℝ} (hr : 0 ≤ r) (hn : 0 < n) : rad (ball n r) = r / Real.sqrt n := by
  have hpow : (0:ℝ) < 2 ^ n := by positivity
  have hsup : ∀ ε : Fin n → Bool, sSup (signAvg ε '' ball n r) = r / Real.sqrt n := by
    intro ε
    obtain ⟨hmem, hval⟩ := ball_attains hn ε
    refine IsGreatest.csSup_eq ⟨⟨_, hmem, hval⟩, ?_⟩
    rintro a ⟨v, hv, rfl⟩
    exact signAvg_le_ball hr hn hv ε
  unfold rad
  rw [Finset.sum_congr rfl fun ε _ => hsup ε, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  push_cast
  field_simp
