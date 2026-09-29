-- Prove2me | Theorems.Thm_Logic_JFeature_one_le_maxRatioStat
-- name    : Logic.JFeature.one_le_maxRatioStat
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:30:35.762326+00:00
-- url     : https://prove2.me/theorems/15584824-0b67-4178-a577-b4461e32f680
-- title:
--   The scan statistic never drops below `1`.
-- statement:
--   **The scan statistic never drops below `1`.**  Pure pigeonhole: some cell
--   always carries at least a proportional share of the hits.
--
--   ```lean
--   theorem Logic.JFeature.one_le_maxRatioStat(u : ι → κ) (Hs : Ω → Finset ι)
--       (hκ : (univ : Finset κ).Nonempty) (hne : ∀ w, (Hs w).Nonempty) (w : Ω) :
--       1 ≤ maxRatioStat u Hs hκ w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/JFeatureSweepSynthesis.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/JFeatureSweepSynthesis.lean#L40

-- Thm stub generated from Logic/JFeatureSweepSynthesis.lean
import Mathlib
import Definitions.Def_Logic_JFeatureMarginalBlindness
import Definitions.Def_Logic_JFeatureMaxStatistic
import Definitions.Def_Logic_JFeatureSweepSynthesis
import Definitions.Def_Logic_PhaseRouteAlignment
/-
# Synthesis: what a flat j-feature sweep does and does not establish

This file ties together the three strands of the paper-248 analysis.

* `pval_maxRatio_eq_one` : the **uncalibrated** scan statistic
  `max_k rate(cell k) / globalRate` is `≥ 1` on *every* draw of the null
  ensemble (pigeonhole, `Logic.JFeature.exists_fiber_rate_ge_globalRate`), so the
  naive test "the best cell exceeds the global rate" has permutation p-value
  exactly `1`.  Only a max-statistic calibration can say anything.
* `sweep_blindness_two_views` : a carrier living in the *joint* structure is
  invisible to marginal features in **two independent statistical views** — the
  contingency view (enrichment ratio exactly `1`, this development) and the
  regression view (degree-1 `R² ≤ 0`, `Logic.PhaseRoute.Rsq_additive_nonpos`).
  Flatness of a marginal sweep is therefore a property of the *test*, not
  evidence about the carrier.
-/

open Logic.JFeature

open Finset


variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]


omit [Fintype Ω] [Nonempty Ω] in

theorem Logic.JFeature.one_le_maxRatioStat(u : ι → κ) (Hs : Ω → Finset ι)
    (hκ : (univ : Finset κ).Nonempty) (hne : ∀ w, (Hs w).Nonempty) (w : Ω) :
    1 ≤ maxRatioStat u Hs hκ w := by sorry
