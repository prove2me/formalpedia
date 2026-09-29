-- Prove2me | solution 1 for RLHFPTX.sq_sd_le_range_mul_mad
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:39:33.536418+00:00
-- url     : https://prove2.me/submissions/23305e51-a930-4f5e-abf6-644ca146c2e7

-- Sol generated from Novelty/RLHFPretrainingMixIn.lean
import Mathlib
import Definitions.Def_Novelty_RLHFPretrainingMixIn

/-!
# The PTX pretraining mix-in creates a `β`-independent alignment floor

Domain: Novelty (information theory × convex analysis × alignment theory).

## The question

Earlier cycles of this thread studied the KL-regularised RLHF optimum
`π_β = argmax_q  𝔼_q[r] − β · KL(q ‖ p)`, whose closed form is the Gibbs tilt
`π_β(y) ∝ p(y) e^{r(y)/β}`, and established the *drift law*
`‖π_β − p‖₁ = Θ(σ_p(r)/β)`: as the KL penalty `β → ∞` the aligned policy returns
to the reference policy `p` at rate `1/β`, with constant the reward standard
deviation.

Production RLHF (InstructGPT-style) adds a **PTX pretraining mix-in**: a fraction
`γ` of pretraining data, drawn from a distribution `d`, is folded back into the
objective.  In the *anchor* formulation adopted here the mix-in replaces the
reference measure by the mixture `p_γ = (1−γ)p + γd`, so the optimum becomes

  `q*_{β,γ}(y) ∝ ((1−γ) p(y) + γ d(y)) · e^{r(y)/β}`.

This file proves the resulting **two-scale drift law**: the total drift away from
the SFT policy `p` splits into a `β`-independent term coming from the mix-in and a
reward-induced term obeying the old `σ/β` law.

## Main results

* `RLHFPTX.l1_mix_self` — `‖p_γ − p‖₁ = γ · ‖d − p‖₁`, exactly.
* `RLHFPTX.gibbs_l1_le_sd` — the reward-induced drift from the *anchor*:
  `‖gibbs β m r − m‖₁ ≤ e^{(M−L)/β} · σ_m(r) / β` for any `L ≤ r ≤ M`.
  (This is the cycle-2 `σ/β` law, reproved here self-containedly.)
* `RLHFPTX.ptx_drift_upper` / `RLHFPTX.ptx_drift_lower` — the two-sided estimate
  `|‖q*_{β,γ} − p‖₁ − γ‖d − p‖₁| ≤ e^{(M−L)/β} σ_{p_γ}(r)/β`.
* `RLHFPTX.ptx_l1_tendsto` — hence `‖q*_{β,γ} − p‖₁ → γ‖d − p‖₁` as `β → ∞`.
* `RLHFPTX.ptx_no_return_to_p` — **the alignment floor**: if `γ > 0` and `d ≠ p`
  then `‖q*_{β,γ} − p‖₁` does *not* tend to `0`; no amount of KL regularisation
  brings the PTX-augmented optimum back to the SFT policy.
* `RLHFPTX.gibbs_beta_l1_tendsto_mad` — the *sharp* constant of the reward-induced
  part: `β · ‖gibbs β m r − m‖₁ → 𝔼_m|r − 𝔼_m r|`, the **mean absolute deviation**,
  not the standard deviation.
* `RLHFPTX.mad_le_sd` and `RLHFPTX.sq_sd_le_range_mul_mad` — the guard that turns
  the sharp constant back into a `Θ(σ/β)` statement:
  `σ²/(M−L) ≤ MAD ≤ σ`.  So the `σ/β` law is two-sided exactly up to the
  dimensionless factor `σ/(M−L)`, and *not* better: the honest first-order
  constant is the MAD.
* `RLHFPTX.ptx_beta_l1_tendsto_mad` — the reward-induced part of the PTX drift,
  measured from the mixture anchor, obeys the same sharp law.
* `RLHFPTX.ptxOpt_optimal` — a Gibbs variational principle showing that `q*_{β,γ}` really
  is the maximiser of the PTX objective `q ↦ 𝔼_q[r] − β KL(q ‖ p_γ)`, so all of the above
  are statements about a genuine optimisation problem, not about an ad hoc formula.
* `RLHFPTX.anchor_return_iff` — model independence: for *any* anchor `m`,
  `‖gibbs β m r − p‖₁ → 0` iff `m = p`; instantiated at the *geometric* mix-in
  `p^{1−γ}d^γ/Z` in `RLHFPTX.geoMix_return_iff`, so the floor is not an artefact of the
  arithmetic mixture model.
* `RLHFPTX.ptx_mean_tendsto` — the tax in reward units: the achieved reward converges to
  `𝔼_p[r] + γ(𝔼_d[r] − 𝔼_p[r])`, a `β`-independent shift.
* `RLHFPTX.ptx_beta_l1_expansion` — the exact `1/β` coefficient of the *total* drift, a
  **signed** covariance `∑_y sgn(p_γ y − p y) p_γ y (r y − 𝔼_{p_γ} r)`; unlike the drift from
  the anchor it can be negative, so reward optimisation may partially cancel the tax.

## Relation to the earlier cycles

The cycle-2 modules that established the `σ/β` law are not part of this snapshot of the
catalog (the files present reference modules that are absent), so this file is written to be
self-contained: it reproves the `σ/β` law it needs, in the same formulation, before
extending it.

## Method

No differentiation of the free energy anywhere.  The reward-induced bound comes
from the elementary convexity estimate `|e^a − e^b| ≤ e^{max a b}|a − b|`
(`RLHFPTX.abs_exp_sub_exp_le`) combined with the variational characterisation
`Var(X) ≤ 𝔼(X − c)²`, and the sharp constant comes from the derivative of
`t ↦ e^{ct}` at `t = 0` transported along `β ↦ 1/β`.
-/

open RLHFPTX

open Finset Real Filter Topology

variable {Ω : Type*} [Fintype Ω]

/-! ## 1. Distributions, moments, and the PTX optimum -/











/-! ## 2. Elementary structure of the objects -/




theorem variance_nonneg {p : Ω → ℝ} (hp : IsDist p) (f : Ω → ℝ) : 0 ≤ variance p f :=
  Finset.sum_nonneg fun y _ => mul_nonneg (hp.1 y) (sq_nonneg _)






/-! ## 3. The partition function and the Gibbs tilt -/




/-! ## 4. The convexity engine -/



/-! ## 5. The reward-induced drift obeys the `σ/β` law -/



theorem mean_le_of_le {m r : Ω → ℝ} (hm : IsDist m) {M : ℝ} (hM : ∀ y, r y ≤ M) :
    mean m r ≤ M := by
  have h : mean m r ≤ ∑ y, m y * M :=
    Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hM y) (hm.1 y)
  rwa [← Finset.sum_mul, hm.2, one_mul] at h

theorem le_mean_of_le {m r : Ω → ℝ} (hm : IsDist m) {L : ℝ} (hL : ∀ y, L ≤ r y) :
    L ≤ mean m r := by
  have h : ∑ y, m y * L ≤ mean m r :=
    Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hL y) (hm.1 y)
  rwa [← Finset.sum_mul, hm.2, one_mul] at h





/-! ## 6. The two-scale PTX drift law -/








/-! ## 7. The sharp constant of the reward-induced drift is the mean absolute deviation -/









/-! ## 8. `q*_{β,γ}` really is the PTX optimum: a Gibbs variational principle

The results above are statements about the *formula* `q*_{β,γ} ∝ p_γ e^{r/β}`.  This section
closes the loop by proving that this formula is exactly the maximiser of the PTX-augmented
RLHF objective `q ↦ 𝔼_q[r] − β KL(q ‖ p_γ)`, so the drift laws above are statements about a
genuine optimum. -/









/-! ## 9. The alignment floor is a property of the anchor, not of the mixture model

The arithmetic mixture `p_γ = (1−γ)p + γd` is one way to model the PTX mix-in.  This section
shows the floor phenomenon is *model independent*: for **any** anchor `m`, the `β → ∞` limit
of `‖gibbs β m r − p‖₁` is exactly `‖m − p‖₁`, so the optimum returns to `p` iff the anchor
*is* `p`.  We then instantiate this at the *geometric* mix-in `p^{1−γ}d^γ / Z`, the anchor
produced by adding a `KL(q ‖ d)` term rather than mixing the data. -/










/-! ## 10. The floor in reward units: a `β`-independent alignment tax

The drift floor is a statement in total variation.  Dualising against the reward itself turns
it into a statement about the *achieved reward*: the mix-in shifts it by the `β`-independent
amount `γ(𝔼_d r − 𝔼_p r)`, which is negative exactly when the pretraining distribution is
worse-rewarded than the SFT policy. -/





/-! ## 11. The exact `1/β` correction to the floor: a signed covariance

Sections 6–7 give `‖q*_{β,γ} − p‖₁ = γ‖d − p‖₁ + O(1/β)` and identify the sharp constant
of the drift *from the anchor*.  Here we identify the exact `1/β` coefficient of the drift
*from `p`* under the nondegeneracy condition that the anchor differs from `p` in every
coordinate.  The coefficient is a **signed** covariance, so — unlike the drift from the
anchor, which is a positive multiple of `MAD` — reward optimisation can *reduce* the total
drift, partially cancelling the pretraining tax. -/








open RLHFPTX in
theorem solution{m r : Ω → ℝ} (hm : IsDist m) {L M : ℝ}
    (hL : ∀ y, L ≤ r y) (hM : ∀ y, r y ≤ M) :
    sd m r ^ 2 ≤ (M - L) * mad m r := by
  have hvar : sd m r ^ 2 = variance m r := Real.sq_sqrt (variance_nonneg hm r)
  rw [hvar, variance, mad, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  have hdev : |r y - mean m r| ≤ M - L := by
    rw [abs_le]
    constructor
    · have := hM y; have := mean_le_of_le hm hM; have := hL y; have := le_mean_of_le hm hL
      linarith
    · have := hM y; have := le_mean_of_le hm hL
      linarith
  have hsq : (r y - mean m r) ^ 2 ≤ (M - L) * |r y - mean m r| := by
    have h1 : (r y - mean m r) ^ 2 = |r y - mean m r| * |r y - mean m r| := by
      rw [← abs_mul, ← sq, abs_of_nonneg (sq_nonneg _)]
    rw [h1]
    exact mul_le_mul_of_nonneg_right hdev (abs_nonneg _)
  calc m y * (r y - mean m r) ^ 2 ≤ m y * ((M - L) * |r y - mean m r|) :=
        mul_le_mul_of_nonneg_left hsq (hm.1 y)
    _ = (M - L) * (m y * |r y - mean m r|) := by ring
