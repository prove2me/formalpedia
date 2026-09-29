-- Prove2me | Definitions.Def_Probability_SpikeStratifiedEvidence
-- name    : Probability_SpikeStratifiedEvidence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:37:45.704116+00:00
-- url     : https://prove2.me/theorems/bacec52b-9a60-448a-99bc-d4da38722637
-- title:
--   Aether Catalog definitions — Probability_SpikeStratifiedEvidence
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SpikeStratifiedEvidence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SpikeStratifiedEvidence.lean by skeleton subtraction
import Mathlib

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

namespace Spike.Evidence

/-- The AICc penalty for `k` parameters on `n` observations,
`2k + 2k(k+1)/(n − k − 1)`. -/
noncomputable def aiccPenalty (k n : ℝ) : ℝ := 2 * k + 2 * k * (k + 1) / (n - k - 1)

/-- `AICc = −2 loglik + penalty`. -/
noncomputable def aicc (loglik k n : ℝ) : ℝ := -2 * loglik + aiccPenalty k n

/-- `ΔAICc` in favour of the enlarged model (`k1` parameters, log-likelihood
`l1`) against the null (`k0`, `l0`) on a sample of size `n`.  Positive values
favour the enlarged model. -/
noncomputable def deltaAICc (l0 l1 k0 k1 n : ℝ) : ℝ := aicc l0 k0 n - aicc l1 k1 n

/-- The penalty difference charged for the extra parameters on a sample of
size `n`. -/
noncomputable def deltaPenalty (k0 k1 n : ℝ) : ℝ := aiccPenalty k1 n - aiccPenalty k0 n



section Stratified

variable {ι Θ : Type*} (S : Finset ι) (ℓ : ι → Θ → ℝ)

/-- Log-likelihood of the pooled sample at a single shared parameter. -/
def pooledLoglik (t : Θ) : ℝ := ∑ i ∈ S, ℓ i t

/-- Log-likelihood of the pooled sample when each stratum uses its own
parameter. -/
def stratifiedLoglik (u : ι → Θ) : ℝ := ∑ i ∈ S, ℓ i (u i)

/-- The **null misspecification gap**: how much better the stratum-wise nulls
fit than the single pooled null (in `2 log` units). -/
def nullGap (t0 : Θ) (u0 : ι → Θ) : ℝ :=
  2 * (stratifiedLoglik S ℓ u0 - pooledLoglik S ℓ t0)



/-- The penalty bookkeeping incurred by splitting: the sum of the stratum-wise
extra-parameter penalties minus the pooled one. -/
noncomputable def penaltyDefect (k0 k1 : ℝ) (nsize : ι → ℝ) (nP : ℝ) : ℝ :=
  (∑ i ∈ S, deltaPenalty k0 k1 (nsize i)) - deltaPenalty k0 k1 nP


end Stratified




end Spike.Evidence


