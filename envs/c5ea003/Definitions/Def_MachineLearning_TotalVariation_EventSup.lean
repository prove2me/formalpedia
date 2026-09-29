-- Prove2me | Definitions.Def_MachineLearning_TotalVariation_EventSup
-- name    : MachineLearning_TotalVariation_EventSup
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:09:50.774981+00:00
-- url     : https://prove2.me/theorems/676a6239-533b-48fa-9f1c-ce3a41a8af54
-- title:
--   Aether Catalog definitions — MachineLearning_TotalVariation_EventSup
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TotalVariation.EventSup`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TotalVariation/EventSup.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
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

namespace UniversalRedundancy

variable {X : Type*} [Fintype X]

/-! ## Events, gaps and the Neyman–Pearson event -/

/-- Probability that the law `p` assigns to the event `A`. -/
def eventProb (p : X → ℝ) (A : Finset X) : ℝ := ∑ x ∈ A, p x

/-- The *distinguishing gap* of an event: how much more likely `A` is under `p`
than under `q`. -/
def eventGap (p q : X → ℝ) (A : Finset X) : ℝ := eventProb p A - eventProb q A







open Classical in
/-- The **Neyman–Pearson event** `{x : q x ≤ p x}`: the likelihood-ratio test at
threshold `1`.  It is the event on which the supremum defining `d_TV` is
attained. -/
noncomputable def sepEvent (p q : X → ℝ) : Finset X := univ.filter fun x => q x ≤ p x

/-! ## The bound and its attainment -/







/-! ## Boolean distinguishers -/

open Classical in
/-- Advantage of a Boolean distinguisher `f`: the difference of its acceptance
probabilities under the two laws. -/
noncomputable def boolAdvantage (p q : X → ℝ) (f : X → Bool) : ℝ :=
  eventGap p q (univ.filter fun x => f x = true)




/-! ## Randomized tests do not help -/


/-! ## The sharp bounded-difference (oscillation) bound -/



/-! ## Comparison with the crude `ℓ¹` bound -/




/-! ## Range and rigid endpoints -/




end UniversalRedundancy


