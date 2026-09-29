-- Prove2me | Theorems.Thm_Spike_Evidence_gap_large_of_strata_below_bar
-- name    : Spike.Evidence.gap_large_of_strata_below_bar
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:06:36.438321+00:00
-- url     : https://prove2.me/theorems/2db9b4fb-48e1-4d60-bf2f-8b5b5738c18f
-- title:
--   Two strata that are individually below the registered bar `6` cannot, by
-- statement:
--   Two strata that are individually below the registered bar `6` cannot, by
--   themselves, produce a pooled statistic above `49`: the remainder is the null
--   gap.  (Contrapositive form of the main inequality.)
--
--   ```lean
--   theorem Spike.Evidence.gap_large_of_strata_below_bar{dPool d1 d2 G defect : ℝ}
--       (hbar1 : d1 ≤ 6) (hbar2 : d2 ≤ 6) (hdef : defect ≤ 3) (hpool : 49 ≤ dPool)
--       (hineq : dPool ≤ d1 + d2 + G + defect) : 34 ≤ G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SpikeStratifiedEvidence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SpikeStratifiedEvidence.lean#L157

-- Thm stub generated from Probability/SpikeStratifiedEvidence.lean
import Mathlib
import Definitions.Def_Probability_SpikeStratifiedEvidence

/-!
# Pooled model-selection evidence versus size-matched strata

Third component of the round-85 resolution.  The empirical situation: a
two-component ("edge") mixture fitted to the *pooled* kept sample reports
`ΔAICc = 49.78`, while the same fit restricted to size-matched strata reports
`ΔAICc = 5.94` (bit-length band `[96, 98)`, i.e. the truncation boundary) and
`ΔAICc = -0.40` (bit-length `≥ 98`).  Both stratum values sit at or below the
registered decision bar `6`.  Is that a contradiction?  No — and this file
proves exactly what the pooled number is then measuring.

Setup.  `ℓ i θ` is the log-likelihood contribution of stratum `i` at parameter
`θ`.  A *pooled* fit chooses one `θ` for all strata; a *stratified* fit chooses
`u i` per stratum.  Write `t0, t1` for pooled maximisers of the null and the
enlarged model, `u0, u1` for the stratum-wise maximisers.

Main results.

* `Spike.Evidence.nullGap_nonneg` — the *null misspecification gap*
  `G = 2(∑ ℓ i (u0 i) − ∑ ℓ i t0) ≥ 0` : a single pooled null can never beat
  stratum-wise nulls.
* `Spike.Evidence.pooled_gain_le` — the pooled evidence for the extra component
  is bounded by the stratified evidence *plus* `G`.  Pooled evidence can
  therefore be arbitrarily large purely because the pooled **null** is
  misspecified across strata.
* `Spike.Evidence.deltaAICc_pooled_le` — the same statement at the level of
  `ΔAICc`, carrying the exact small-sample penalty bookkeeping
  (`penaltyDefect`).
* `Spike.Evidence.nullGap_ge_of_reported` — the quantitative reading of the
  reported numbers: with `ΔAICc` pooled `49.78`, strata `5.94` and `−0.40`, and
  a penalty defect of at most `3`, the misspecification gap satisfies
  `G ≥ 41.2`.  Over `80 %` of the pooled "evidence" is null heterogeneity
  (a size gradient across bit-length bands), not support for the extra
  component.
* `Spike.Evidence.aiccPenalty_lt_of_lt` — splitting a sample into strata
  strictly *raises* the small-sample penalty, so the stratified analysis is the
  conservative one; sub-bar strata are not an artefact of a laxer criterion.
* `Spike.Evidence.exists_pooled_above_bar_strata_below` — an explicit
  configuration in which every stratum is below the bar `6` while the pooled
  statistic exceeds `49`, realised entirely by null heterogeneity.
-/

open Spike.Evidence








variable {ι Θ : Type*} (S : Finset ι) (ℓ : ι → Θ → ℝ)

theorem Spike.Evidence.gap_large_of_strata_below_bar{dPool d1 d2 G defect : ℝ}
    (hbar1 : d1 ≤ 6) (hbar2 : d2 ≤ 6) (hdef : defect ≤ 3) (hpool : 49 ≤ dPool)
    (hineq : dPool ≤ d1 + d2 + G + defect) : 34 ≤ G := by sorry
