-- Prove2me | solution 1 for RLHFPTX.gibbs_l1_le_sd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:38:04.85385+00:00
-- url     : https://prove2.me/submissions/adf4c277-7fad-4d52-921f-8b9f20221d5d

-- Sol generated from Novelty/RLHFPretrainingMixIn.lean
import Mathlib
import Definitions.Def_Novelty_RLHFPretrainingMixIn
import Theorems.Thm_RLHFPTX_abs_mean_le_sqrt
import Theorems.Thm_RLHFPTX_variance_tilt_le

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





theorem sd_nonneg (p f : Ω → ℝ) : 0 ≤ sd p f := Real.sqrt_nonneg _





/-! ## 3. The partition function and the Gibbs tilt -/

theorem partf_pos {m : Ω → ℝ} (hm : IsDist m) (r : Ω → ℝ) (β : ℝ) : 0 < partf β m r := by
  obtain ⟨y, hy⟩ : ∃ y : Ω, 0 < m y := by
    by_contra h
    push_neg at h
    have : ∑ y, m y = 0 := by
      refine Finset.sum_eq_zero fun y _ => le_antisymm (h y) (hm.1 y)
    rw [hm.2] at this; norm_num at this
  refine Finset.sum_pos' (fun z _ => mul_nonneg (hm.1 z) (Real.exp_pos _).le) ⟨y, mem_univ y, ?_⟩
  exact mul_pos hy (Real.exp_pos _)


/-- Explicit form of the pointwise deviation of the Gibbs tilt from its anchor. -/
theorem gibbs_sub_anchor {m : Ω → ℝ} (hm : IsDist m) (r : Ω → ℝ) (β : ℝ) (y : Ω) :
    gibbs β m r y - m y = m y * (Real.exp (r y / β) - partf β m r) / partf β m r := by
  have hZ := partf_pos hm r β
  unfold gibbs
  field_simp

/-! ## 4. The convexity engine -/



/-! ## 5. The reward-induced drift obeys the `σ/β` law -/





/-- The partition function is bounded below by `e^{L/β}` when `r ≥ L`. -/
theorem exp_le_partf {m r : Ω → ℝ} (hm : IsDist m) {L β : ℝ} (hβ : 0 < β)
    (hL : ∀ y, L ≤ r y) : Real.exp (L / β) ≤ partf β m r := by
  have h : ∑ y, m y * Real.exp (L / β) ≤ partf β m r := by
    refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (hm.1 y)
    exact Real.exp_le_exp.mpr (by gcongr; exact hL y)
  rwa [← Finset.sum_mul, hm.2, one_mul] at h

/-- The `ℓ¹` drift of the Gibbs tilt from its anchor, in mean-deviation form. -/
theorem gibbs_l1_eq {m : Ω → ℝ} (hm : IsDist m) (r : Ω → ℝ) (β : ℝ) :
    l1 (gibbs β m r) m
      = (∑ y, m y * |Real.exp (r y / β) - partf β m r|) / partf β m r := by
  have hZ := partf_pos hm r β
  rw [l1, Finset.sum_div]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [gibbs_sub_anchor hm r β y, abs_div, abs_of_pos hZ, abs_mul, abs_of_nonneg (hm.1 y)]



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
theorem solution{m r : Ω → ℝ} (hm : IsDist m) {L M β : ℝ} (hβ : 0 < β)
    (hL : ∀ y, L ≤ r y) (hM : ∀ y, r y ≤ M) :
    l1 (gibbs β m r) m ≤ Real.exp ((M - L) / β) * sd m r / β := by
  have hZ := partf_pos hm r β
  -- numerator estimate: `𝔼_m|u − 𝔼_m u| ≤ σ_m(u) ≤ (e^{M/β}/β) σ_m(r)`
  have hmeanu : mean m (fun y => Real.exp (r y / β)) = partf β m r := rfl
  have step1 : (∑ y, m y * |Real.exp (r y / β) - partf β m r|)
      ≤ Real.sqrt (variance m (fun y => Real.exp (r y / β))) := by
    have h := abs_mean_le_sqrt hm (fun y => Real.exp (r y / β) - partf β m r)
    simpa [variance, hmeanu] using h
  have step2 : Real.sqrt (variance m (fun y => Real.exp (r y / β)))
      ≤ Real.exp (M / β) / β * sd m r := by
    refine le_trans (Real.sqrt_le_sqrt (variance_tilt_le hm hβ hM)) ?_
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    rfl
  have hnum : (∑ y, m y * |Real.exp (r y / β) - partf β m r|)
      ≤ Real.exp (M / β) / β * sd m r := le_trans step1 step2
  rw [gibbs_l1_eq hm r β]
  have hfinal : (∑ y, m y * |Real.exp (r y / β) - partf β m r|) / partf β m r
      ≤ (Real.exp (M / β) / β * sd m r) / Real.exp (L / β) := by
    exact div_le_div₀ (mul_nonneg (by positivity) (sd_nonneg _ _)) hnum (Real.exp_pos _)
      (exp_le_partf hm hβ hL)
  refine le_trans hfinal (le_of_eq ?_)
  rw [sub_div, Real.exp_sub]
  field_simp
