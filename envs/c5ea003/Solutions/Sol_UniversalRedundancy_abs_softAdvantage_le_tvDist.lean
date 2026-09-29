-- Prove2me | solution 1 for UniversalRedundancy.abs_softAdvantage_le_tvDist
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:24:33.163521+00:00
-- url     : https://prove2.me/submissions/94bb1d13-e331-4ffa-b700-44739b287140

-- Sol generated from MachineLearning/TotalVariation/EventSup.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_EventSup
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Theorems.Thm_UniversalRedundancy_SourceClass_sum_posPart_eq_tvDist
import Theorems.Thm_UniversalRedundancy_tvDist_comm
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
    {g : X → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    |∑ x, (p x - q x) * g x| ≤ tvDist p q := by
  have key : ∀ r s : X → ℝ, (∑ x, r x = 1) → (∑ x, s x = 1) →
      ∑ x, (r x - s x) * g x ≤ tvDist r s := by
    intro r s hr hs
    rw [← SourceClass.sum_posPart_eq_tvDist hr hs]
    refine Finset.sum_le_sum fun x _ => ?_
    rcases le_total (s x) (r x) with h | h
    · have hmax : max (r x - s x) 0 = r x - s x := max_eq_left (by linarith)
      rw [hmax]
      nlinarith [hg1 x, hg0 x]
    · have h0 : (0:ℝ) ≤ max (r x - s x) 0 := le_max_right _ _
      nlinarith [hg0 x]
  rcases abs_cases (∑ x, (p x - q x) * g x) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; exact key p q hp hq
  · rw [h]
    have hneg : -∑ x, (p x - q x) * g x = ∑ x, (q x - p x) * g x := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hneg, tvDist_comm]
    exact key q p hq hp
