-- Prove2me | Theorems.Thm_Probability_AdaptiveQS_approx_dial_retention
-- name    : Probability.AdaptiveQS.approx_dial_retention
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:52:44.338548+00:00
-- url     : https://prove2.me/theorems/4d984b13-f21a-4f09-b222-990c55d12a76
-- title:
--   The flip survives a miscalibrated dial.
-- statement:
--   **The flip survives a miscalibrated dial.**  If the dial is within `ε` of the true
--   rate on every target, threshold skipping retains the work-proportional yield up to a
--   degradation `2ε |K| |D|`.  A perfect dial (`ε = 0`) recovers
--   `retention_ge_work_fraction`.
--
--   ```lean
--   theorem Probability.AdaptiveQS.approx_dial_retention{s : Finset ι} {d r : ι → ℝ} {ε : ℝ}
--       (hε : ∀ i ∈ s, |d i - r i| ≤ ε) (θ : ℝ) :
--       ((keepSet s d θ).card : ℝ) * (∑ i ∈ s, r i)
--         ≤ (s.card : ℝ) * (∑ i ∈ keepSet s d θ, r i)
--           + 2 * ε * (keepSet s d θ).card * (skipSet s d θ).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AdaptiveQSSkipFlip.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AdaptiveQSSkipFlip.lean#L216

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












/-! ## An imperfect dial: the quantitative flip -/

theorem Probability.AdaptiveQS.approx_dial_retention{s : Finset ι} {d r : ι → ℝ} {ε : ℝ}
    (hε : ∀ i ∈ s, |d i - r i| ≤ ε) (θ : ℝ) :
    ((keepSet s d θ).card : ℝ) * (∑ i ∈ s, r i)
      ≤ (s.card : ℝ) * (∑ i ∈ keepSet s d θ, r i)
        + 2 * ε * (keepSet s d θ).card * (skipSet s d θ).card := by sorry
