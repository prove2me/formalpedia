-- Prove2me | solution 1 for UniversalRedundancy.tvDist_eq_one_iff_singular
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:40:57.926039+00:00
-- url     : https://prove2.me/submissions/f27f5dbb-8917-4fdf-8edb-d046003a6a35

-- Sol generated from MachineLearning/TotalVariation/EventSup.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_EventSup
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Theorems.Thm_UniversalRedundancy_SourceClass_sum_min_eq_one_sub_tvDist
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
theorem solution{p q : X → ℝ} (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) :
    tvDist p q = 1 ↔ ∀ x, p x = 0 ∨ q x = 0 := by
  have hmin := SourceClass.sum_min_eq_one_sub_tvDist hp hq
  constructor
  · intro h1 x
    rw [h1] at hmin
    have hz : ∑ y, min (p y) (q y) = 0 := by linarith
    have hx := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => le_min (hp0 y) (hq0 y))).mp hz x (Finset.mem_univ x)
    rcases min_cases (p x) (q x) with ⟨he, _⟩ | ⟨he, _⟩
    · exact Or.inl (by rw [← he]; exact hx)
    · exact Or.inr (by rw [← he]; exact hx)
  · intro hsing
    have hz : ∑ y, min (p y) (q y) = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      rcases hsing y with h | h
      · rw [h, min_eq_left (hq0 y)]
      · rw [h, min_eq_right (hp0 y)]
    linarith
