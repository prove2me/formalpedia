-- Prove2me | solution 1 for UniversalRedundancy.exists_expectation_diff_eq_osc_mul_tvDist
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:25:04.139461+00:00
-- url     : https://prove2.me/submissions/87d4f6e2-7e61-477a-b1be-34d7690b6a81

-- Sol generated from MachineLearning/TotalVariation/EventSup.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_EventSup
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Theorems.Thm_UniversalRedundancy_eventGap_sepEvent
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
theorem solution{p q : X → ℝ}
    (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) :
    ∃ g : X → ℝ, (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ 1) ∧
      ∑ x, p x * g x - ∑ x, q x * g x = (1 - 0) * tvDist p q := by
  classical
  refine ⟨fun x => if x ∈ sepEvent p q then 1 else 0, fun x => by positivity,
    fun x => by by_cases h : x ∈ sepEvent p q <;> simp [h], ?_⟩
  have hind : ∀ r : X → ℝ, ∑ x, r x * (if x ∈ sepEvent p q then (1:ℝ) else 0)
      = eventProb r (sepEvent p q) := by
    intro r
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter, eventProb]
  rw [hind p, hind q, sub_zero, one_mul, ← eventGap, eventGap_sepEvent hp hq]
