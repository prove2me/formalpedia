-- Prove2me | solution 1 for UniversalRedundancy.abs_expectation_diff_le_osc_mul_tvDist
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:27:44.189665+00:00
-- url     : https://prove2.me/submissions/9ed65109-4e26-4900-a5a5-ce002e940bfb

-- Sol generated from MachineLearning/TotalVariation/EventSup.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_EventSup
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Theorems.Thm_UniversalRedundancy_abs_softAdvantage_le_tvDist
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sharp normalization for total variation: the event-supremum characterization

The catalog already carries the *arithmetic* half of total variation: the file
`MachineLearning.UniversalRedundancy.Rigidity` defines

`d_TV(p, q) = (∑ₓ |p x − q x|) / 2`

and uses it to price universal codes.  What the catalog does **not** carry is
the *operational* half — the reason for the factor `1/2`.  This file supplies
it, in the sharp (attained) form:

`d_TV(p, q) = max_{A ⊆ X} (p(A) − q(A))`.

Everything downstream is then tight rather than off by the customary factor of
two that one gets from the lazy `ℓ¹` estimate
`|p(A) − q(A)| ≤ ∑ₓ |p x − q x| = 2 d_TV(p, q)`.

## Main results

* `eventGap_le_tvDist`, `abs_eventGap_le_tvDist` — every event is `d_TV`-bounded;
* `eventGap_sepEvent` — the Neyman–Pearson event `{q ≤ p}` attains the bound;
* `isGreatest_eventGap`, `tvDist_eq_sSup_eventGap`, `tvDist_eq_iSup_eventGap` —
  the supremum characterization, in `IsGreatest`, `sSup` and `⨆` form;
* `isGreatest_boolAdvantage`, `tvDist_eq_iSup_boolAdvantage` — the same statement
  read as the optimal advantage of a Boolean distinguisher;
* `abs_softAdvantage_le_tvDist` — randomized `[0,1]`-valued tests do no better
  than Boolean ones (the extreme points of the test polytope are deterministic);
* `abs_expectation_diff_le_osc_mul_tvDist` — the sharp bounded-difference form:
  `|E_p g − E_q g| ≤ (M − m)·d_TV` for `m ≤ g ≤ M`, with the sharpness witness
  `exists_expectation_diff_eq_osc_mul_tvDist`;
* `tvDist_lt_l1_of_ne` — the `ℓ¹` bound is *strictly* lossy whenever `p ≠ q`,
  quantifying exactly what the sharper normalization buys;
* `tvDist_le_one`, `tvDist_eq_zero_iff`, `tvDist_eq_one_iff_singular` — the range
  and the two rigid endpoints, now with operational readings.

## Application keywords

total variation, statistical distance, Neyman–Pearson, distinguishing advantage,
hypothesis testing, indistinguishability, sample complexity
-/


open Finset

open UniversalRedundancy

variable {X : Type*} [Fintype X]

/-! ## Events, gaps and the Neyman–Pearson event -/










/-! ## The bound and its attainment -/







/-! ## Boolean distinguishers -/





/-! ## Randomized tests do not help -/


/-! ## The sharp bounded-difference (oscillation) bound -/



/-! ## Comparison with the crude `ℓ¹` bound -/




/-! ## Range and rigid endpoints -/





open UniversalRedundancy in
theorem solution{p q : X → ℝ} [Nonempty X]
    (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) {g : X → ℝ} {m M : ℝ}
    (hm : ∀ x, m ≤ g x) (hM : ∀ x, g x ≤ M) :
    |∑ x, p x * g x - ∑ x, q x * g x| ≤ (M - m) * tvDist p q := by
  have hmM : m ≤ M := le_trans (hm (Classical.arbitrary X)) (hM (Classical.arbitrary X))
  have hrew : ∑ x, p x * g x - ∑ x, q x * g x = ∑ x, (p x - q x) * (g x - m) := by
    have h0 : ∑ x, (p x - q x) = 0 := by
      rw [Finset.sum_sub_distrib, hp, hq]; ring
    have hexp : ∑ x, (p x - q x) * (g x - m)
        = (∑ x, (p x - q x) * g x) - m * ∑ x, (p x - q x) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hexp, h0, mul_zero, sub_zero, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rcases eq_or_lt_of_le hmM with heq | hlt
  · have hconst : ∀ x, g x - m = 0 := fun x => by
      have h1 := hm x; have h2 := hM x; rw [← heq] at h2; linarith
    rw [hrew, Finset.sum_congr rfl fun x _ => by rw [hconst x, mul_zero]]
    rw [← heq]
    simp
  · have hpos : 0 < M - m := by linarith
    have hh0 : ∀ x, 0 ≤ (g x - m) / (M - m) :=
      fun x => div_nonneg (by linarith [hm x]) (le_of_lt hpos)
    have hh1 : ∀ x, (g x - m) / (M - m) ≤ 1 :=
      fun x => (div_le_one hpos).mpr (by linarith [hM x])
    have hsoft := abs_softAdvantage_le_tvDist hp hq hh0 hh1
    have hfac : ∑ x, (p x - q x) * (g x - m)
        = (M - m) * ∑ x, (p x - q x) * ((g x - m) / (M - m)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      field_simp
    rw [hrew, hfac, abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_left hsoft (le_of_lt hpos)
