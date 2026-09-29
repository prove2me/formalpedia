-- Prove2me | solution 1 for RLHFPTX.ptx_no_return_to_p
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:39:33.032223+00:00
-- url     : https://prove2.me/submissions/73890b8f-91a1-4622-993e-7042b401f9e6

-- Sol generated from Novelty/RLHFPretrainingMixIn.lean
import Mathlib
import Definitions.Def_Novelty_RLHFPretrainingMixIn
import Theorems.Thm_RLHFPTX_gibbs_l1_le_sd

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


theorem l1_comm (f g : Ω → ℝ) : l1 f g = l1 g f :=
  Finset.sum_congr rfl fun _ _ => abs_sub_comm _ _

theorem l1_triangle (f g h : Ω → ℝ) : l1 f h ≤ l1 f g + l1 g h := by
  rw [l1, l1, l1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  have hy : f y - h y = (f y - g y) + (g y - h y) := by ring
  rw [hy]
  exact abs_add_le _ _




/-- The mixture of two distributions is a distribution. -/
theorem mix_isDist {p d : Ω → ℝ} (hp : IsDist p) (hd : IsDist d) {γ : ℝ}
    (h0 : 0 ≤ γ) (h1 : γ ≤ 1) : IsDist (mix γ p d) := by
  constructor
  · intro y
    have := hp.1 y; have := hd.1 y
    have : (0:ℝ) ≤ 1 - γ := by linarith
    unfold mix; positivity
  · unfold mix
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.2, hd.2]
    ring

/-- **The mix-in drift is exactly `γ‖d − p‖₁`.** -/
theorem l1_mix_self (p d : Ω → ℝ) {γ : ℝ} (h0 : 0 ≤ γ) : l1 (mix γ p d) p = γ * l1 d p := by
  unfold l1 mix
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have : (1 - γ) * p y + γ * d y - p y = γ * (d y - p y) := by ring
  rw [this, abs_mul, abs_of_nonneg h0]


/-! ## 3. The partition function and the Gibbs tilt -/




/-! ## 4. The convexity engine -/



/-! ## 5. The reward-induced drift obeys the `σ/β` law -/









/-! ## 6. The two-scale PTX drift law -/

/-- **Upper half of the two-scale law.** The total drift of the PTX optimum away from the
SFT policy `p` is at most the mix-in drift `γ‖d − p‖₁` plus the reward drift `O(σ/β)`. -/
theorem ptx_drift_upper {p d r : Ω → ℝ} (hp : IsDist p) (hd : IsDist d) {γ L M β : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hβ : 0 < β) (hL : ∀ y, L ≤ r y) (hM : ∀ y, r y ≤ M) :
    l1 (ptxOpt β γ p d r) p
      ≤ γ * l1 d p + Real.exp ((M - L) / β) * sd (mix γ p d) r / β := by
  have hmix := mix_isDist hp hd hγ0 hγ1
  have h1 := l1_triangle (ptxOpt β γ p d r) (mix γ p d) p
  have h2 := gibbs_l1_le_sd (r := r) hmix hβ hL hM
  rw [l1_mix_self p d hγ0] at h1
  unfold ptxOpt at h1 ⊢
  linarith

/-- **Lower half of the two-scale law.** The mix-in drift cannot be cancelled: the total
drift is at least `γ‖d − p‖₁` minus the reward drift. -/
theorem ptx_drift_lower {p d r : Ω → ℝ} (hp : IsDist p) (hd : IsDist d) {γ L M β : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hβ : 0 < β) (hL : ∀ y, L ≤ r y) (hM : ∀ y, r y ≤ M) :
    γ * l1 d p - Real.exp ((M - L) / β) * sd (mix γ p d) r / β
      ≤ l1 (ptxOpt β γ p d r) p := by
  have hmix := mix_isDist hp hd hγ0 hγ1
  have h1 := l1_triangle (mix γ p d) (ptxOpt β γ p d r) p
  have h2 := gibbs_l1_le_sd (r := r) hmix hβ hL hM
  rw [l1_mix_self p d hγ0, l1_comm (mix γ p d) (ptxOpt β γ p d r)] at h1
  unfold ptxOpt at h1 ⊢
  linarith

/-- **The two-scale drift law**, in one statement:
`| ‖q*_{β,γ} − p‖₁ − γ‖d − p‖₁ | ≤ e^{(M−L)/β} σ_{p_γ}(r) / β`. -/
theorem ptx_drift_two_sided {p d r : Ω → ℝ} (hp : IsDist p) (hd : IsDist d) {γ L M β : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hβ : 0 < β) (hL : ∀ y, L ≤ r y) (hM : ∀ y, r y ≤ M) :
    |l1 (ptxOpt β γ p d r) p - γ * l1 d p|
      ≤ Real.exp ((M - L) / β) * sd (mix γ p d) r / β := by
  rw [abs_le]
  constructor
  · have := ptx_drift_lower hp hd hγ0 hγ1 hβ hL hM; linarith
  · have := ptx_drift_upper hp hd hγ0 hγ1 hβ hL hM; linarith

/-- `e^{c/β} → 1` as `β → ∞`. -/
theorem tendsto_exp_div_one (c : ℝ) :
    Filter.Tendsto (fun β : ℝ => Real.exp (c / β)) Filter.atTop (nhds 1) := by
  have hb : Filter.Tendsto (fun β : ℝ => c / β) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  simpa using (Real.continuous_exp.tendsto 0).comp hb

/-- The `σ/β` envelope vanishes as `β → ∞`. -/
theorem tendsto_drift_bound (K C : ℝ) :
    Filter.Tendsto (fun β : ℝ => Real.exp (K / β) * C / β) Filter.atTop (nhds 0) := by
  simpa using
    Filter.Tendsto.div_atTop ((tendsto_exp_div_one K).mul (tendsto_const_nhds (x := C)))
      Filter.tendsto_id

/-- **The alignment floor.** As `β → ∞` the PTX-augmented optimum does not return to the
SFT policy `p`: its `ℓ¹` distance from `p` converges to the strictly positive constant
`γ‖d − p‖₁` whenever `γ > 0` and `d ≠ p`. -/
theorem ptx_l1_tendsto {p d r : Ω → ℝ} (hp : IsDist p) (hd : IsDist d) {γ L M : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hL : ∀ y, L ≤ r y) (hM : ∀ y, r y ≤ M) :
    Filter.Tendsto (fun β : ℝ => l1 (ptxOpt β γ p d r) p) Filter.atTop
      (nhds (γ * l1 d p)) := by
  have hzero : Filter.Tendsto
      (fun β : ℝ => l1 (ptxOpt β γ p d r) p - γ * l1 d p) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_drift_bound (M - L) (sd (mix γ p d) r))
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with β hβ
    simpa [Real.norm_eq_abs] using ptx_drift_two_sided hp hd hγ0 hγ1 hβ hL hM
  simpa using hzero.add (tendsto_const_nhds (x := γ * l1 d p))


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
theorem solution{p d r : Ω → ℝ} (hp : IsDist p) (hd : IsDist d) {γ L M : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hL : ∀ y, L ≤ r y) (hM : ∀ y, r y ≤ M)
    (hdp : d ≠ p) :
    ¬ Filter.Tendsto (fun β : ℝ => l1 (ptxOpt β γ p d r) p) Filter.atTop (nhds 0) := by
  intro hcon
  have hlim := ptx_l1_tendsto hp hd hγ0.le hγ1 hL hM
  have heq : γ * l1 d p = 0 := tendsto_nhds_unique hlim hcon
  have hl1 : l1 d p = 0 := by
    rcases mul_eq_zero.1 heq with h | h
    · exact absurd h hγ0.ne'
    · exact h
  refine hdp (funext fun y => ?_)
  have hy : |d y - p y| = 0 := by
    have hnn : ∀ z ∈ (Finset.univ : Finset Ω), 0 ≤ |d z - p z| := fun z _ => abs_nonneg _
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hl1 y (Finset.mem_univ y)
  have := abs_eq_zero.1 hy
  linarith
