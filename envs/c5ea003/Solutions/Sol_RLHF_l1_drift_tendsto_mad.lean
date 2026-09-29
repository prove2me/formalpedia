-- Prove2me | solution 1 for RLHF.l1_drift_tendsto_mad
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:27:35.907513+00:00
-- url     : https://prove2.me/submissions/fd743996-3b1b-4841-b862-e97a441c6b56

-- Sol generated from Algebra/RLHFMeanAbsoluteDeviation.lean
import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFMeanAbsoluteDeviation
import Theorems.Thm_RLHF_l1_drift_lower_mad
import Theorems.Thm_RLHF_l1_drift_upper_mad

/-!
# The sharp alignment-drift constant is the mean absolute deviation

Domain: Algebra (convex analysis × information theory × alignment theory).

Conjecture **C1** of the drift thread said that the constant in the `Θ(β⁻¹)` alignment
drift law `‖π_β − p‖₁ ≲ c/β` is the reward *standard deviation* `σ_p(r)`, refining the
earlier reward-*range* constant; the catalogue proves
`‖π_β − p‖₁ ≤ √(2 e^{range r/β} Var_p r)/β` and sandwiches an explicit family between
`σ/(2β)` and `3σ/β`.  What was left open was **the absolute constant**.

This file settles it, and the answer is *not* `σ_p(r)`.  The exact first-order drift
constant is the **mean absolute deviation**

  `MAD_p(r) = 𝔼_p |r − 𝔼_p r| ≤ σ_p(r)`,

with a *quantitative, non-asymptotic* two-sided estimate valid as soon as the
temperature exceeds the reward range:

* `RLHF.l1_drift_upper_mad` — `‖π_β − p‖₁ ≤ MAD_p(r)/β + 2 Var_p(r)/β²`;
* `RLHF.l1_drift_lower_mad` — `‖π_β − p‖₁ ≥ MAD_p(r)/β − 3 Var_p(r)/β²`;
* `RLHF.l1_drift_tendsto_mad` — hence `β·‖π_β − p‖₁ → MAD_p(r)` as `β → ∞`, so the
  constant `1` is attained by `MAD` and by no smaller functional.

The comparison with C1 is exact, via the *deviation defect identity*
`Var_p(r) − MAD_p(r)² = 𝔼_p(|r − 𝔼r| − MAD)²`:

* `RLHF.mad_le_sqrt_variance` — `MAD_p(r) ≤ σ_p(r)` always, so the σ-law of C1 is
  never violated;
* `RLHF.mad_eq_sqrt_variance_iff` — equality holds **iff** `|r − 𝔼_p r|` is constant,
  i.e. exactly for the balanced two-valued rewards.  This explains why the two-point
  family of `RLHF.variance_constant_optimal` saturated the σ-law: it is the unique
  saturating shape.
* `RLHF.mad_sq_spike_eq` — on the rare-spike family `p(true) = ε`, `r = 1_{true}`,
  `MAD² = 4ε(1−ε)·Var`, so the σ-constant is off by the unbounded factor
  `1/(2√(ε(1−ε)))`: the MAD law is *strictly*, and unboundedly, sharper.

The proof is a centred second-order expansion of the exponential tilt: writing
`u = r − 𝔼_p r`, `s = u/β` and `W = 𝔼_p e^{s}`, one has `π_β = p e^{s}/W`, `W ≥ 1` by
Jensen, `W ≤ 1 + Var/β²` by the quadratic Taylor bound `|e^x − 1 − x| ≤ x²` for
`|x| ≤ 1`, and the triangle inequality transfers `|e^{s} − W| ≈ |s|` termwise.
-/

open RLHF

open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## 1. The deviation defect identity: `MAD ≤ σ` and its equality case -/





variable [Nonempty Ω]


/-! ## 2. The centred tilt normaliser -/





/-! ## 3. The Gibbs policy in centred form -/




/-! ## 4. The sharp two-sided drift law -/





/-! ## 5. Separation from the standard-deviation law: the rare-spike family -/










open RLHF in
theorem solution{r p : Ω → ℝ} (hp : IsPosDist p) :
    Filter.Tendsto (fun β : ℝ => β * l1Dist (gibbsPolicy β r p) p) Filter.atTop
      (nhds (mad p r)) := by
  have hlow : Filter.Tendsto (fun β : ℝ => mad p r - 3 * (variance p r / β)) Filter.atTop
      (nhds (mad p r)) := by
    have h0 : Filter.Tendsto (fun β : ℝ => variance p r / β) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
    have h : Filter.Tendsto (fun β : ℝ => 3 * (variance p r / β)) Filter.atTop (nhds 0) := by
      simpa using h0.const_mul (3 : ℝ)
    simpa using tendsto_const_nhds.sub h
  have hhigh : Filter.Tendsto (fun β : ℝ => mad p r + 2 * (variance p r / β)) Filter.atTop
      (nhds (mad p r)) := by
    have h0 : Filter.Tendsto (fun β : ℝ => variance p r / β) Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
    have h : Filter.Tendsto (fun β : ℝ => 2 * (variance p r / β)) Filter.atTop (nhds 0) := by
      simpa using h0.const_mul (2 : ℝ)
    simpa using tendsto_const_nhds.add h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (max (rewardRange r) 1)] with β hβm
    have hβ : 0 < β := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hβm)
    have hr : rewardRange r ≤ β := le_trans (le_max_left _ _) hβm
    have h := mul_le_mul_of_nonneg_left (l1_drift_lower_mad hβ hp hr) hβ.le
    calc mad p r - 3 * (variance p r / β)
        = β * (mad p r / β - 3 * (variance p r / β ^ 2)) := by field_simp
      _ ≤ β * l1Dist (gibbsPolicy β r p) p := h
  · filter_upwards [Filter.eventually_ge_atTop (max (rewardRange r) 1)] with β hβm
    have hβ : 0 < β := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hβm)
    have hr : rewardRange r ≤ β := le_trans (le_max_left _ _) hβm
    have h := mul_le_mul_of_nonneg_left (l1_drift_upper_mad hβ hp hr) hβ.le
    calc β * l1Dist (gibbsPolicy β r p) p
        ≤ β * (mad p r / β + 2 * (variance p r / β ^ 2)) := h
      _ = mad p r + 2 * (variance p r / β) := by field_simp
