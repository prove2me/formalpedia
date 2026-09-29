-- Prove2me | solution 1 for RLHFPTX.anchor_beta_l1_expansion
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:32:47.220636+00:00
-- url     : https://prove2.me/submissions/3409e280-60ae-4252-93cb-2f407c69140d

-- Sol generated from Novelty/RLHFPretrainingMixIn.lean
import Mathlib
import Definitions.Def_Novelty_RLHFPretrainingMixIn
import Theorems.Thm_RLHFPTX_tendsto_beta_mul_exp_sub_one
import Theorems.Thm_RLHFPTX_tendsto_beta_mul_partf_sub_one

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









/-! ## 6. The two-scale PTX drift law -/




/-- `e^{c/β} → 1` as `β → ∞`. -/
theorem tendsto_exp_div_one (c : ℝ) :
    Filter.Tendsto (fun β : ℝ => Real.exp (c / β)) Filter.atTop (nhds 1) := by
  have hb : Filter.Tendsto (fun β : ℝ => c / β) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  simpa using (Real.continuous_exp.tendsto 0).comp hb




/-! ## 7. The sharp constant of the reward-induced drift is the mean absolute deviation -/


/-- The partition function tends to `1` as `β → ∞`. -/
theorem tendsto_partf_one {m : Ω → ℝ} (hm : IsDist m) (r : Ω → ℝ) :
    Filter.Tendsto (fun β : ℝ => partf β m r) Filter.atTop (nhds 1) := by
  have h : Filter.Tendsto (fun β : ℝ => ∑ y, m y * Real.exp (r y / β)) Filter.atTop
      (nhds (∑ _y : Ω, m _y * 1)) :=
    tendsto_finset_sum _ fun y _ => tendsto_const_nhds.mul (tendsto_exp_div_one (r y))
  simpa [partf, hm.2] using h


/-- Each coordinate of the rescaled deviation converges to the centred reward. -/
theorem tendsto_beta_mul_dev {m : Ω → ℝ} (hm : IsDist m) (r : Ω → ℝ) (y : Ω) :
    Filter.Tendsto (fun β : ℝ => β * (Real.exp (r y / β) - partf β m r)) Filter.atTop
      (nhds (r y - mean m r)) := by
  refine ((tendsto_beta_mul_exp_sub_one (r y)).sub
    (tendsto_beta_mul_partf_sub_one hm r)).congr fun β => by ring





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


omit [Fintype Ω] in
theorem abs_eq_sgnAt_mul {f g : Ω → ℝ} {y : Ω} (h : g y ≠ f y) :
    |f y - g y| = sgnAt f g y * (f y - g y) := by
  unfold sgnAt
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [if_pos hlt, one_mul, abs_of_pos (by linarith)]
  · rw [if_neg (by linarith), abs_of_neg (by linarith)]
    ring

/-- The Gibbs tilt converges pointwise to its anchor. -/
theorem tendsto_gibbs_pointwise {m : Ω → ℝ} (hm : IsDist m) (r : Ω → ℝ) (y : Ω) :
    Filter.Tendsto (fun β : ℝ => gibbs β m r y) Filter.atTop (nhds (m y)) := by
  have h : Filter.Tendsto (fun β : ℝ => m y * Real.exp (r y / β) / partf β m r) Filter.atTop
      (nhds (m y * 1 / 1)) :=
    (tendsto_const_nhds.mul (tendsto_exp_div_one (r y))).div (tendsto_partf_one hm r) one_ne_zero
  simpa [gibbs] using h

/-- The rescaled pointwise drift converges to the centred reward weighted by the anchor. -/
theorem tendsto_beta_mul_gibbs_sub {m : Ω → ℝ} (hm : IsDist m) (r : Ω → ℝ) (y : Ω) :
    Filter.Tendsto (fun β : ℝ => β * (gibbs β m r y - m y)) Filter.atTop
      (nhds (m y * (r y - mean m r))) := by
  have h : Filter.Tendsto
      (fun β : ℝ => m y * (β * (Real.exp (r y / β) - partf β m r)) / partf β m r)
      Filter.atTop (nhds (m y * (r y - mean m r) / 1)) :=
    (tendsto_const_nhds.mul (tendsto_beta_mul_dev hm r y)).div (tendsto_partf_one hm r)
      one_ne_zero
  rw [div_one] at h
  refine h.congr fun β => ?_
  rw [gibbs_sub_anchor hm r β y]
  field_simp




open RLHFPTX in
theorem solution{m p r : Ω → ℝ} (hm : IsDist m) (hne : ∀ y, p y ≠ m y) :
    Filter.Tendsto (fun β : ℝ => β * (l1 (gibbs β m r) p - l1 m p)) Filter.atTop
      (nhds (∑ y, sgnAt m p y * (m y * (r y - mean m r)))) := by
  have hsum : Filter.Tendsto
      (fun β : ℝ => ∑ y, sgnAt m p y * (β * (gibbs β m r y - m y))) Filter.atTop
      (nhds (∑ y, sgnAt m p y * (m y * (r y - mean m r)))) :=
    tendsto_finset_sum _ fun y _ =>
      tendsto_const_nhds.mul (tendsto_beta_mul_gibbs_sub hm r y)
  refine hsum.congr' ?_
  have hev : ∀ y : Ω, ∀ᶠ β : ℝ in Filter.atTop,
      |gibbs β m r y - p y| = sgnAt m p y * (gibbs β m r y - p y) := by
    intro y
    have hq := tendsto_gibbs_pointwise hm r y
    unfold sgnAt
    rcases lt_or_gt_of_ne (hne y) with hlt | hgt
    · rw [if_pos hlt]
      filter_upwards [hq.eventually_const_lt hlt] with β hβ
      rw [one_mul, abs_of_pos (by linarith)]
    · rw [if_neg (by linarith)]
      filter_upwards [hq.eventually_lt_const hgt] with β hβ
      rw [abs_of_neg (by linarith)]; ring
  filter_upwards [Filter.eventually_all.2 hev] with β hβ
  have h1 : l1 (gibbs β m r) p = ∑ y, sgnAt m p y * (gibbs β m r y - p y) :=
    Finset.sum_congr rfl fun y _ => hβ y
  have h2 : l1 m p = ∑ y, sgnAt m p y * (m y - p y) :=
    Finset.sum_congr rfl fun y _ => abs_eq_sgnAt_mul (hne y)
  rw [h1, h2, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring
