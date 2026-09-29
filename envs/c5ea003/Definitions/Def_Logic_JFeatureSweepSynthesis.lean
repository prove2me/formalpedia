-- Prove2me | Definitions.Def_Logic_JFeatureSweepSynthesis
-- name    : Logic_JFeatureSweepSynthesis
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:55:52.117547+00:00
-- url     : https://prove2.me/theorems/85355d97-e52b-42d5-a968-648d404d0cca
-- title:
--   Aether Catalog definitions — Logic_JFeatureSweepSynthesis
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.JFeatureSweepSynthesis`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/JFeatureSweepSynthesis.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_JFeatureMarginalBlindness
import Definitions.Def_Logic_JFeatureMaxStatistic
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

namespace Logic.JFeature

open Finset

section NaiveScan

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- The raw (uncalibrated) scan statistic of a sweep: the largest cell-to-global
rate ratio over the scanned feature cells, evaluated on a null draw `w` whose
hit set is `Hs w`. -/
noncomputable def maxRatioStat (u : ι → κ) (Hs : Ω → Finset ι)
    (hκ : (univ : Finset κ).Nonempty) (w : Ω) : ℝ :=
  (univ : Finset κ).sup' hκ
    (fun k => rate (Hs w) (univ.filter (fun i => u i = k)) / globalRate (Hs w))



end NaiveScan

section TwoViews

open Logic.PhaseRoute

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable [Nonempty α] [Nonempty β]



end TwoViews

end Logic.JFeature


