-- Prove2me | Theorems.Thm_Probability_AdaptiveQS_concordant_self
-- name    : Probability.AdaptiveQS.concordant_self
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:53:14.867817+00:00
-- url     : https://prove2.me/theorems/68db86cd-6d09-4c9d-80ba-0f598fbc8e8d
-- title:
--   The true rate is trivially concordant with itself: the oracle dial.
-- statement:
--   The true rate is trivially concordant with itself: the oracle dial.
--
--   ```lean
--   theorem Probability.AdaptiveQS.concordant_self(s : Finset ι) (r : ι → ℝ) : Concordant s r r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AdaptiveQSSkipFlip.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AdaptiveQSSkipFlip.lean#L161

-- Thm stub generated from Probability/AdaptiveQSSkipFlip.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSSkipFlip
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Skip-flip wins, and the quadratic-residue null equaliser

Companion to `Probability.AdaptiveQSAllocation`.  That file shows that spending a
*fixed* budget in inverse proportion to a predicted rate must lose.  Experiment 559
then flipped the deployment: instead of reallocating sieve length, use the same
dial to **skip** the worst targets (`θ = q20` skipped `28.3%` of the work while
retaining `89.5%` of the relations, a `+28.9%` throughput gain), and defer the hard
tail (`40/400` targets that no amount of sieving reaches).

This file proves that the flip is not a lucky calibration but a theorem, in three
layers.

1. **Separation ⇒ retention beats work fraction.**  `sum_le_of_separated_slack` is
   the general engine: if every kept target beats every skipped target up to a slack
   `c`, then `|K| · (total yield) ≤ |s| · (kept yield) + c |K| |D|`.  With `c = 0`
   (`retention_ge_work_fraction`) this says exactly `retention ≥ work fraction`, i.e.
   the throughput ratio is `≥ 1`; `skip_throughput_ge` and `skip_throughput_gt` state
   it as a mean comparison, the latter strictly.

2. **An imperfect dial still wins, quantitatively.**  `approx_dial_retention` runs
   the same engine with `c = 2ε` for a dial that is only `ε`-accurate — the measured
   Spearman `0.739 < 1` costs at most a `2ε` degradation term, and
   `approx_dial_threshold_gain` gives the explicit condition on `ε` under which the
   skip still wins.  This is the robustness statement the deployment needs.

3. **The null equaliser is exact arithmetic, not statistics.**  A prime `p` for which
   `N` is a quadratic *non*-residue divides **no** value `x² - N`
   (`nonresidue_not_dvd_qsValue`), so its sieve hit rate is identically zero
   (`hitRate_eq_zero_of_nonresidue`) — the hard tail is unreachable by construction.
   `qs_null_equalizer` then says the yield of *any* allocation is unchanged by
   deleting the null targets, and `transfer_from_null_lt` says that moving any
   positive amount of budget off a null target onto a live one strictly increases the
   yield.  Deferral, not deeper sieving, is the instrument.
-/

open Probability.AdaptiveQS

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ## The separation engine -/




/-! ## The deployment flip: threshold skipping -/








omit [DecidableEq ι] in

theorem Probability.AdaptiveQS.concordant_self(s : Finset ι) (r : ι → ℝ) : Concordant s r r := by sorry
