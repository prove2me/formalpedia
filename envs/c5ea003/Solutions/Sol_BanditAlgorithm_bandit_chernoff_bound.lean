-- Prove2me | solution 1 for BanditAlgorithm.bandit_chernoff_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T20:25:18.473422+00:00
-- url     : https://prove2.me/submissions/2adf811a-56e2-4788-b2dd-c9ed9228c54c

import Theorems.Thm_BanditAlgorithm_banditTrajMeasure_joint_eq_compProd
import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic


/-!
# The Kullback–Leibler divergence between two real Gaussians of equal variance

`D(𝒩(a, v) ‖ 𝒩(b, v)) = (a − b)² / (2v)`.

This is the quantitative input of every fixed-confidence best-arm-identification
bound over the Gaussian class: the characteristic time `c*(ν)` of L&S Eq. (33.4)
is defined through `klDiv`, while the Track-and-Stop statistic `Z_t` is written in
the closed form `½ · T_a T_b/(T_a + T_b) · (μ̂_a − μ̂_b)²`, and the two are related
exactly by this identity.  Mathlib computes the mean and the variance of
`gaussianReal` but not its relative entropy.

The proof is the textbook one.  Both measures have a strictly positive density
against Lebesgue measure, so `d𝒩(a,v)/d𝒩(b,v) = pdf_a / pdf_b` Lebesgue-a.e. and
hence `𝒩(a,v)`-a.e., and the log-likelihood ratio collapses to an *affine*
function of `x`:

  `llr x = ((x − b)² − (x − a)²)/(2v) = (a − b)(2x − a − b)/(2v)`.

Only the first moment of a Gaussian is therefore needed, and `∫ x d𝒩(a,v) = a`
gives `(a − b)(2a − a − b)/(2v) = (a − b)²/(2v)`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {v : ℝ≥0}

theorem nnreal_coe_pos_of_ne_zero (hv : v ≠ 0) : (0 : ℝ) < (v : ℝ) := by
  have : (0 : ℝ≥0) < v := lt_of_le_of_ne bot_le (Ne.symm hv)
  exact_mod_cast this

/-! ## 1. The logarithm of the Gaussian density -/

theorem log_gaussianPDFReal (hv : v ≠ 0) (m x : ℝ) :
    Real.log (gaussianPDFReal m v x)
      = -Real.log (√(2 * π * v)) - (x - m) ^ 2 / (2 * v) := by
  have hvR : (0 : ℝ) < (v : ℝ) := nnreal_coe_pos_of_ne_zero hv
  have hs : (0 : ℝ) < √(2 * π * v) := Real.sqrt_pos.mpr (by positivity)
  rw [gaussianPDFReal, Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_inv, Real.log_exp]
  ring

/-- The log-likelihood ratio of two Gaussians with the same variance is affine. -/
theorem log_gaussianPDFReal_sub (hv : v ≠ 0) (a b x : ℝ) :
    Real.log (gaussianPDFReal a v x) - Real.log (gaussianPDFReal b v x)
      = (a - b) * (2 * x - a - b) / (2 * v) := by
  have hvR : (0 : ℝ) < (v : ℝ) := nnreal_coe_pos_of_ne_zero hv
  rw [log_gaussianPDFReal hv, log_gaussianPDFReal hv]
  field_simp
  ring

/-! ## 2. The Radon–Nikodym derivative -/

theorem rnDeriv_gaussianReal_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    (gaussianReal a v).rnDeriv (gaussianReal b v)
      =ᵐ[volume] fun x ↦ (gaussianPDF b v x)⁻¹ * gaussianPDF a v x := by
  have hb : gaussianReal b v = volume.withDensity (gaussianPDF b v) :=
    gaussianReal_of_var_ne_zero _ hv
  have h1 : (gaussianReal a v).rnDeriv (volume.withDensity (gaussianPDF b v))
      =ᵐ[volume] fun x ↦ (gaussianPDF b v x)⁻¹ * (gaussianReal a v).rnDeriv volume x := by
    refine Measure.rnDeriv_withDensity_right _ _ (measurable_gaussianPDF b v).aemeasurable
      (Filter.Eventually.of_forall fun x ↦ (gaussianPDF_pos b hv x).ne')
      (Filter.Eventually.of_forall fun x ↦ ?_)
    simp [gaussianPDF]
  have h2 : (gaussianReal a v).rnDeriv volume =ᵐ[volume] gaussianPDF a v :=
    rnDeriv_gaussianReal a v
  rw [hb]
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2]

/-- The log-likelihood ratio of two same-variance Gaussians, `𝒩(a,v)`-almost
everywhere. -/
theorem llr_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    llr (gaussianReal a v) (gaussianReal b v)
      =ᵐ[gaussianReal a v] fun x ↦ (a - b) * (2 * x - a - b) / (2 * v) := by
  have hac : gaussianReal a v ≪ volume := gaussianReal_absolutelyContinuous a hv
  have hae : ∀ᵐ x ∂(gaussianReal a v), (gaussianReal a v).rnDeriv (gaussianReal b v) x
      = (gaussianPDF b v x)⁻¹ * gaussianPDF a v x :=
    hac.ae_le (rnDeriv_gaussianReal_gaussianReal hv a b)
  filter_upwards [hae] with x hx
  have hbpos : 0 < gaussianPDFReal b v x := gaussianPDFReal_pos b v x hv
  have hapos : 0 < gaussianPDFReal a v x := gaussianPDFReal_pos a v x hv
  rw [llr, hx, ENNReal.toReal_mul, gaussianPDF, gaussianPDF,
    ← ENNReal.ofReal_inv_of_pos hbpos, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal hapos.le, Real.log_mul (by positivity) hapos.ne', Real.log_inv,
    ← log_gaussianPDFReal_sub hv a b x]
  ring

/-! ## 3. Integrability and the integral -/

/-- `x ↦ x` is integrable against a Gaussian. -/
theorem integrable_id_gaussianReal (m : ℝ) (w : ℝ≥0) :
    Integrable (fun x : ℝ ↦ x) (gaussianReal m w) := by
  have h : Integrable id (gaussianReal m w) :=
    MemLp.integrable (by norm_num) (memLp_id_gaussianReal (μ := m) (v := w) 1)
  simpa [Function.id_def] using h

/-- The affine function appearing as the log-likelihood ratio. -/
theorem integrable_llr_form (hv : v ≠ 0) (a b : ℝ) :
    Integrable (fun x : ℝ ↦ (a - b) * (2 * x - a - b) / (2 * v)) (gaussianReal a v) := by
  have hid := integrable_id_gaussianReal a v
  have h1 : Integrable (fun x : ℝ ↦ 2 * x - a - b) (gaussianReal a v) :=
    (((hid.const_mul 2).sub (integrable_const a)).sub (integrable_const b))
  exact (h1.const_mul (a - b)).div_const (2 * v)

theorem integrable_llr_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    Integrable (llr (gaussianReal a v) (gaussianReal b v)) (gaussianReal a v) :=
  (integrable_llr_form hv a b).congr (llr_gaussianReal hv a b).symm

theorem integral_llr_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    ∫ x, llr (gaussianReal a v) (gaussianReal b v) x ∂(gaussianReal a v)
      = (a - b) ^ 2 / (2 * v) := by
  have hvR : (0 : ℝ) < (v : ℝ) := nnreal_coe_pos_of_ne_zero hv
  have hid := integrable_id_gaussianReal a v
  rw [integral_congr_ae (llr_gaussianReal hv a b)]
  have hrw : (fun x : ℝ ↦ (a - b) * (2 * x - a - b) / (2 * v))
      = fun x : ℝ ↦ ((a - b) / (v : ℝ)) * x - (a - b) * (a + b) / (2 * v) := by
    funext x
    field_simp
    ring
  rw [hrw, integral_sub (hid.const_mul _) (integrable_const _), integral_const_mul,
    integral_id_gaussianReal]
  simp only [integral_const, smul_eq_mul, measureReal_univ_eq_one, one_mul]
  field_simp
  ring

/-! ## 4. The divergence -/

/-- **The Kullback–Leibler divergence between two Gaussians of equal variance.** -/
theorem klDiv_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    klDiv (gaussianReal a v) (gaussianReal b v)
      = ENNReal.ofReal ((a - b) ^ 2 / (2 * v)) := by
  have hac : gaussianReal a v ≪ gaussianReal b v := by
    refine (gaussianReal_absolutelyContinuous a hv).trans ?_
    exact gaussianReal_absolutelyContinuous' b hv
  rw [klDiv_of_ac_of_integrable hac (integrable_llr_gaussianReal hv a b),
    integral_llr_gaussianReal hv a b]
  simp

/-- The unit-variance case, which is the environment class `𝓔^k_𝒩(1)` of L&S
Chapter 33. -/
theorem klDiv_gaussianReal_one (a b : ℝ) :
    klDiv (gaussianReal a 1) (gaussianReal b 1)
      = ENNReal.ofReal ((a - b) ^ 2 / 2) := by
  rw [klDiv_gaussianReal one_ne_zero a b]
  norm_num

end BanditAlgorithm



/-!
# The one-step exponential (martingale) identity for the bandit trajectory

This is the foundational brick that the three remaining leaves of Theorem 33.6 all
need: it is the *only* place where the conditional law of a reward given the past
enters, and once it is available the rest of the concentration argument is
martingale bookkeeping.

For a unit-variance Gaussian bandit, an arbitrary sampling rule, an arbitrary
`𝓕_n`-measurable weight `F`, an arm `a` and a parameter `λ`:

  `E[ F(prefix_n) · exp(λ(X_{n+1} − μ_a) − λ²/2)^{1{A_{n+1} = a}} ] = E[ F(prefix_n) ]`.

In other words `exp(λ(S_a(n) − T_a(n)μ_a) − λ²T_a(n)/2)` is a martingale, which is
the starting point of every self-normalised deviation bound (and hence of
`chernoff_pairwise_selfnormalised_deviation_bound`, of Garivier–Kaufmann's
Proposition 13, and — through the strong law it yields — of the D-Tracking
convergence statement).

The proof is exactly the decomposition the model was built for:

* `banditTrajMeasure_joint_eq_compProd` (already Proved) turns the expectation of a
  function of `(prefix_n, round_{n+1})` into an integral against
  `P_n ⊗ₘ banditStepKernel`;
* `banditStepKernel = (π.select n) ⊗ₖ (banditRewardKernel ∘ snd)` splits that into
  "choose the arm, then draw the reward";
* the inner reward integral is `1` for every arm — trivially if the arm is not `a`,
  and by the Gaussian moment generating function `∫ e^{λx} d𝒩(μ,1) = e^{λμ+λ²/2}`
  if it is.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-- The tilt factor `exp(λ(x − μ) − λ²/2)` integrates to `1` against `𝒩(μ, 1)`. -/
theorem lintegral_expTilt_gaussianReal (m lam : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (lam * (x - m) - lam ^ 2 / 2))
        ∂(gaussianReal m 1) = 1 := by
  have hint : Integrable (fun x : ℝ ↦ Real.exp (lam * (x - m) - lam ^ 2 / 2))
      (gaussianReal m 1) := by
    have h := integrable_exp_mul_gaussianReal (μ := m) (v := 1) lam
    have hrw : (fun x : ℝ ↦ Real.exp (lam * (x - m) - lam ^ 2 / 2))
        = fun x : ℝ ↦ Real.exp (-(lam * m) - lam ^ 2 / 2) * Real.exp (lam * x) := by
      funext x
      rw [← Real.exp_add]
      ring_nf
    rw [hrw]
    exact h.const_mul _
  have hval : ∫ x, Real.exp (lam * (x - m) - lam ^ 2 / 2) ∂(gaussianReal m 1) = 1 := by
    have hrw : (fun x : ℝ ↦ Real.exp (lam * (x - m) - lam ^ 2 / 2))
        = fun x : ℝ ↦ Real.exp (-(lam * m) - lam ^ 2 / 2) * Real.exp (lam * x) := by
      funext x
      rw [← Real.exp_add]
      ring_nf
    rw [hrw, integral_const_mul]
    have hmgf : ∫ x, Real.exp (lam * x) ∂(gaussianReal m 1)
        = Real.exp (m * lam + (1 : ℝ≥0) * lam ^ 2 / 2) := by
      have := mgf_fun_id_gaussianReal (μ := m) (v := 1)
      have h2 := congrFun this lam
      rw [mgf] at h2
      simpa using h2
    rw [hmgf, ← Real.exp_add]
    rw [show -(lam * m) - lam ^ 2 / 2 + (m * lam + ((1 : ℝ≥0) : ℝ) * lam ^ 2 / 2) = 0 by
      push_cast; ring]
    exact Real.exp_zero
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le), hval,
    ENNReal.ofReal_one]

/-- The tilt factor, as a function of a whole round. -/
noncomputable def expTilt (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) (y : Fin k × ℝ) : ℝ≥0∞ :=
  if y.1 = a then ENNReal.ofReal (Real.exp (lam * (y.2 - μvec a) - lam ^ 2 / 2)) else 1

theorem measurable_expTilt (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) :
    Measurable (expTilt μvec a lam) := by
  classical
  unfold expTilt
  refine Measurable.ite (measurable_fst (measurableSet_singleton a)) ?_ measurable_const
  have h1 : Measurable fun y : Fin k × ℝ ↦ lam * (y.2 - μvec a) - lam ^ 2 / 2 :=
    ((measurable_snd.sub_const (μvec a)).const_mul lam).sub_const (lam ^ 2 / 2)
  exact ENNReal.measurable_ofReal.comp h1.exp

/-- The tilt integrates to `1` against the reward distribution of any arm. -/
theorem lintegral_expTilt_arm (μvec : Fin k → ℝ) (a b : Fin k) (lam : ℝ) :
    ∫⁻ x, expTilt μvec a lam (b, x) ∂(gaussianReal (μvec b) 1) = 1 := by
  classical
  by_cases hb : b = a
  · subst hb
    have hfun : (fun x : ℝ ↦ expTilt μvec b lam (b, x))
        = fun x : ℝ ↦ ENNReal.ofReal (Real.exp (lam * (x - μvec b) - lam ^ 2 / 2)) := by
      funext x; simp [expTilt]
    rw [hfun, lintegral_expTilt_gaussianReal]
  · have hfun : (fun x : ℝ ↦ expTilt μvec a lam (b, x)) = fun _ : ℝ ↦ (1 : ℝ≥0∞) := by
      funext x; simp [expTilt, hb]
    rw [hfun, lintegral_one, measure_univ]

/-- The tilt integrates to `1` against one round of the Gaussian bandit. -/
theorem lintegral_expTilt_stepKernel (μvec : Fin k → ℝ) (pol : BanditPolicy k) (n : ℕ)
    (a : Fin k) (lam : ℝ) (h : BanditHistory k n) :
    ∫⁻ y, expTilt μvec a lam y ∂(banditStepKernel (gaussianBandit μvec) pol n h) = 1 := by
  classical
  rw [banditStepKernel, Kernel.lintegral_compProd _ _ _ (measurable_expTilt μvec a lam)]
  have hrk : ∀ b : Fin k,
      banditRewardKernel (gaussianBandit μvec) b = gaussianReal (μvec b) 1 := fun _ ↦ rfl
  simp only [Kernel.comap_apply, hrk]
  refine Eq.trans (lintegral_congr (g := fun _ : Fin k ↦ (1 : ℝ≥0∞)) fun b ↦ ?_) ?_
  · exact lintegral_expTilt_arm μvec a b lam
  · rw [lintegral_one, measure_univ]

/-- **The one-step exponential identity.** -/
theorem lintegral_mul_expTilt (μvec : Fin k → ℝ) (pol : BanditPolicy k) (n : ℕ)
    (a : Fin k) (lam : ℝ) (F : BanditHistory k n → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F (banditTrajPrefix k n ω) * expTilt μvec a lam (ω n)
        ∂(banditTrajMeasure (gaussianBandit μvec) pol)
      = ∫⁻ ω, F (banditTrajPrefix k n ω)
        ∂(banditTrajMeasure (gaussianBandit μvec) pol) := by
  classical
  set ν : StochasticBandit k := gaussianBandit μvec with hν
  set P : Measure (ℕ → Fin k × ℝ) := banditTrajMeasure ν pol with hP
  set G : BanditHistory k n × (Fin k × ℝ) → ℝ≥0∞ := fun p ↦ F p.1 * expTilt μvec a lam p.2
    with hG
  have hGmeas : Measurable G :=
    (hF.comp measurable_fst).mul ((measurable_expTilt μvec a lam).comp measurable_snd)
  have hmap : Measurable (fun ω : ℕ → Fin k × ℝ ↦ (banditTrajPrefix k n ω, ω n)) :=
    measurable_banditTrajPrefix.prodMk (measurable_pi_apply n)
  -- rewrite the left side as an integral against the joint law
  have hL : ∫⁻ ω, F (banditTrajPrefix k n ω) * expTilt μvec a lam (ω n) ∂P
      = ∫⁻ p, G p ∂(P.map (fun ω ↦ (banditTrajPrefix k n ω, ω n))) := by
    rw [lintegral_map hGmeas hmap]
  rw [hL, banditTrajMeasure_joint_eq_compProd ν pol n,
    Measure.lintegral_compProd hGmeas]
  have hinner : ∀ h : BanditHistory k n,
      ∫⁻ y, G (h, y) ∂(banditStepKernel ν pol n h) = F h := by
    intro h
    have : (fun y ↦ G (h, y)) = fun y ↦ F h * expTilt μvec a lam y := rfl
    rw [this, lintegral_const_mul _ (measurable_expTilt μvec a lam),
      lintegral_expTilt_stepKernel μvec pol n a lam h, mul_one]
  simp only [hinner]
  -- and the right side is the same integral against the prefix law
  rw [lintegral_map hF measurable_banditTrajPrefix]

/-- The one-step identity with the tilt written out, for use as a standalone
statement. -/
theorem lintegral_mul_expTilt' (μvec : Fin k → ℝ) (pol : BanditPolicy k) (n : ℕ)
    (a : Fin k) (lam : ℝ) (F : BanditHistory k n → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F (banditTrajPrefix k n ω) *
        (if (ω n).1 = a then
          ENNReal.ofReal (Real.exp (lam * ((ω n).2 - μvec a) - lam ^ 2 / 2)) else 1)
        ∂(banditTrajMeasure (gaussianBandit μvec) pol)
      = ∫⁻ ω, F (banditTrajPrefix k n ω)
        ∂(banditTrajMeasure (gaussianBandit μvec) pol) :=
  lintegral_mul_expTilt μvec pol n a lam F hF

end BanditAlgorithm



/-!
# Elementary algebra of the trajectory statistics

Pull counts, empirical means and empirical allocations, and the identities that
every part of the Track-and-Stop analysis uses:

* `trajPullCount_succ` — the one-round recursion `T_i(t+1) = T_i(t) + 1{A_{t+1} = i}`;
* `sum_trajPullCount` — `∑_i T_i(t) = t`;
* `trajPullCount_le` — `T_i(t) ≤ t`, and monotonicity in `t`;
* `sum_trajAllocation` — the empirical allocation lies in the simplex for `t > 0`;
* `trajEmpiricalMean_eq_zero_of_pullCount_eq_zero` — the junk value convention;
* `trajRewardSum_eq` — `∑ rewards = T_i(t) · μ̂_i(t)` when `T_i(t) > 0`.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

namespace BanditAlgorithm

variable {k : ℕ}

/-- The sum of the rewards collected from arm `i` in the first `t` rounds. -/
noncomputable def trajRewardSum (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) : ℝ :=
  ∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2

theorem trajEmpiricalMean_eq (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajEmpiricalMean i t ω = trajRewardSum i t ω / (trajPullCount i t ω : ℝ) := rfl

/-! ## Pull counts -/

@[simp]
theorem trajPullCount_zero (i : Fin k) (ω : ℕ → Fin k × ℝ) : trajPullCount i 0 ω = 0 := by
  simp [trajPullCount]

theorem trajPullCount_succ (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPullCount i (t + 1) ω =
      trajPullCount i t ω + if (ω t).1 = i then 1 else 0 := by
  classical
  simp only [trajPullCount, Finset.range_add_one, Finset.filter_insert]
  by_cases h : (ω t).1 = i
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp), if_pos h]
  · rw [if_neg h, if_neg h, add_zero]

theorem trajRewardSum_succ (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajRewardSum i (t + 1) ω =
      trajRewardSum i t ω + if (ω t).1 = i then (ω t).2 else 0 := by
  classical
  simp only [trajRewardSum, Finset.range_add_one, Finset.filter_insert]
  by_cases h : (ω t).1 = i
  · rw [if_pos h, Finset.sum_insert (by simp), if_pos h, add_comm]
  · rw [if_neg h, if_neg h, add_zero]

theorem trajPullCount_mono (i : Fin k) {s t : ℕ} (h : s ≤ t) (ω : ℕ → Fin k × ℝ) :
    trajPullCount i s ω ≤ trajPullCount i t ω := by
  classical
  refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
  exact fun x hx ↦ Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)

theorem trajPullCount_le (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPullCount i t ω ≤ t := by
  classical
  calc trajPullCount i t ω ≤ (Finset.range t).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = t := Finset.card_range t

/-- The pull counts of the `k` arms partition the rounds: `∑_i T_i(t) = t`. -/
theorem sum_trajPullCount (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    ∑ i : Fin k, trajPullCount i t ω = t := by
  classical
  induction t with
  | zero => simp
  | succ t ih =>
      simp only [trajPullCount_succ, Finset.sum_add_distrib, ih]
      congr 1
      simp

/-- Some arm is played at least `t / k` times. -/
theorem exists_trajPullCount_ge (hk : 0 < k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    ∃ i : Fin k, t ≤ k * trajPullCount i t ω := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k))
    (fun i ↦ trajPullCount i t ω) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  calc t = ∑ j : Fin k, trajPullCount j t ω := (sum_trajPullCount t ω).symm
    _ ≤ ∑ _j : Fin k, trajPullCount i t ω :=
        Finset.sum_le_sum fun j _ ↦ hi j (Finset.mem_univ j)
    _ = k * trajPullCount i t ω := by simp [mul_comm]

/-! ## Empirical allocations -/

@[simp]
theorem trajAllocation_eq (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajAllocation i t ω = (trajPullCount i t ω : ℝ) / (t : ℝ) := rfl

theorem trajAllocation_nonneg (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    0 ≤ trajAllocation i t ω :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem trajAllocation_le_one (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajAllocation i t ω ≤ 1 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [trajAllocation]
  · rw [trajAllocation_eq, div_le_one (by exact_mod_cast ht)]
    exact_mod_cast trajPullCount_le i t ω

/-- For `t > 0` the empirical allocation lies in the probability simplex. -/
theorem sum_trajAllocation {t : ℕ} (ht : 0 < t) (ω : ℕ → Fin k × ℝ) :
    ∑ i : Fin k, trajAllocation i t ω = 1 := by
  have htR : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  simp only [trajAllocation_eq, ← Finset.sum_div]
  rw [← Nat.cast_sum, sum_trajPullCount t ω]
  exact div_self htR

/-! ## Empirical means -/

theorem trajEmpiricalMean_of_pullCount_eq_zero {i : Fin k} {t : ℕ} {ω : ℕ → Fin k × ℝ}
    (h : trajPullCount i t ω = 0) : trajEmpiricalMean i t ω = 0 := by
  simp [trajEmpiricalMean, h]

theorem trajRewardSum_eq_mul (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ)
    (h : trajPullCount i t ω ≠ 0) :
    trajRewardSum i t ω = (trajPullCount i t ω : ℝ) * trajEmpiricalMean i t ω := by
  have hne : ((trajPullCount i t ω : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h
  rw [trajEmpiricalMean_eq, mul_div_cancel₀ _ hne]

/-! ## The pairwise GLR statistic -/

theorem trajPairGLR_comm (a b : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPairGLR a b t ω = trajPairGLR b a t ω := by
  simp only [trajPairGLR]
  rw [mul_comm ((trajPullCount a t ω : ℕ) : ℝ) ((trajPullCount b t ω : ℕ) : ℝ),
    add_comm ((trajPullCount a t ω : ℕ) : ℝ) ((trajPullCount b t ω : ℕ) : ℝ),
    ← neg_sub (trajEmpiricalMean a t ω) (trajEmpiricalMean b t ω), neg_pow]
  ring

theorem trajPairGLR_nonneg (a b : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    0 ≤ trajPairGLR a b t ω := by
  refine div_nonneg (mul_nonneg (div_nonneg (mul_nonneg ?_ ?_) ?_) (sq_nonneg _)) (by norm_num)
  · exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _
  · positivity

theorem trajPairGLR_self (a : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPairGLR a a t ω = 0 := by
  simp [trajPairGLR]

end BanditAlgorithm



/-!
# The exponential martingale of a Gaussian bandit has expectation one

Iterating the one-step identity of `OneStepMGF` gives, for every arm `a`, every
`λ` and every round `n`,

  `E[ exp( λ (S_a(n) − T_a(n) μ_a) − λ² T_a(n) / 2 ) ] = 1`,

where `S_a(n)` is the sum of the rewards collected from arm `a` in the first `n`
rounds and `T_a(n)` is the number of times it was played.  Markov's inequality
then turns this into the fixed-round Chernoff bound that the self-normalised
deviation estimate is built from.

The induction step is exactly the one-step identity: the weight at round `n+1`
factorises as (weight at round `n`, a function of the prefix) times the tilt of
round `n+1`, because `S_a` and `T_a` both increase by the round's contribution
only when arm `a` is played.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. History-level pull counts and reward sums -/

/-- The number of times arm `a` was played, as a function of the history. -/
def histPullCount (a : Fin k) {n : ℕ} (hst : BanditHistory k n) : ℕ :=
  ∑ t : Fin n, if (hst t).1 = a then 1 else 0

/-- The sum of the rewards collected from arm `a`, as a function of the history. -/
noncomputable def histRewardSum (a : Fin k) {n : ℕ} (hst : BanditHistory k n) : ℝ :=
  ∑ t : Fin n, if (hst t).1 = a then (hst t).2 else 0

theorem histPullCount_prefix (a : Fin k) (n : ℕ) (ω : ℕ → Fin k × ℝ) :
    histPullCount a (banditTrajPrefix k n ω) = trajPullCount a n ω := by
  classical
  rw [histPullCount, trajPullCount, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun s ↦ if (ω s).1 = a then 1 else 0) n

theorem histRewardSum_prefix (a : Fin k) (n : ℕ) (ω : ℕ → Fin k × ℝ) :
    histRewardSum a (banditTrajPrefix k n ω) = trajRewardSum a n ω := by
  classical
  rw [histRewardSum, trajRewardSum, Finset.sum_filter]
  exact Fin.sum_univ_eq_sum_range (fun s ↦ if (ω s).1 = a then (ω s).2 else 0) n

theorem measurable_histPullCount (a : Fin k) (n : ℕ) :
    Measurable (histPullCount (k := k) a (n := n)) := by
  classical
  refine Finset.measurable_sum _ fun t _ ↦ ?_
  exact Measurable.ite ((measurable_fst.comp (measurable_pi_apply t))
    (measurableSet_singleton a)) measurable_const measurable_const

theorem measurable_histRewardSum (a : Fin k) (n : ℕ) :
    Measurable (histRewardSum (k := k) a (n := n)) := by
  classical
  refine Finset.measurable_sum _ fun t _ ↦ ?_
  exact Measurable.ite ((measurable_fst.comp (measurable_pi_apply t))
    (measurableSet_singleton a)) (measurable_snd.comp (measurable_pi_apply t)) measurable_const

/-! ## 2. The weight -/

/-- The exponential weight `exp(λ(S_a − T_a μ_a) − λ² T_a/2)` on histories. -/
noncomputable def expWeight (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) {n : ℕ}
    (hst : BanditHistory k n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (lam * (histRewardSum a hst - (histPullCount a hst : ℝ) * μvec a)
    - lam ^ 2 * (histPullCount a hst : ℝ) / 2))

theorem measurable_expWeight (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) (n : ℕ) :
    Measurable (expWeight (k := k) μvec a lam (n := n)) := by
  unfold expWeight
  refine ENNReal.measurable_ofReal.comp (Measurable.exp ?_)
  have h1 : Measurable fun hst : BanditHistory k n ↦ (histPullCount a hst : ℝ) :=
    measurable_from_top.comp (measurable_histPullCount a n)
  exact (((measurable_histRewardSum a n).sub (h1.mul measurable_const)).const_mul lam).sub
    ((h1.const_mul (lam ^ 2)).div_const 2)

/-- The one-round recursion of the weight. -/
theorem expWeight_succ (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) :
    expWeight μvec a lam (banditTrajPrefix k (n + 1) ω)
      = expWeight μvec a lam (banditTrajPrefix k n ω) *
        (if (ω n).1 = a then
          ENNReal.ofReal (Real.exp (lam * ((ω n).2 - μvec a) - lam ^ 2 / 2)) else 1) := by
  classical
  unfold expWeight
  rw [histPullCount_prefix, histPullCount_prefix, histRewardSum_prefix, histRewardSum_prefix,
    trajPullCount_succ, trajRewardSum_succ]
  by_cases h : (ω n).1 = a
  · rw [if_pos h, if_pos h, if_pos h, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    push_cast
    ring
  · rw [if_neg h, if_neg h, if_neg h, mul_one]
    congr 2
    push_cast
    ring

/-! ## 3. Expectation one -/

/-- **The exponential martingale has expectation one.** -/
theorem lintegral_expWeight (μvec : Fin k → ℝ) (pol : BanditPolicy k) (a : Fin k)
    (lam : ℝ) (n : ℕ) :
    ∫⁻ ω, expWeight μvec a lam (banditTrajPrefix k n ω)
        ∂(banditTrajMeasure (gaussianBandit μvec) pol) = 1 := by
  induction n with
  | zero =>
      have h0 : ∀ ω : ℕ → Fin k × ℝ,
          expWeight μvec a lam (banditTrajPrefix k 0 ω) = 1 := by
        intro ω
        unfold expWeight histPullCount histRewardSum
        simp
      simp only [h0]
      rw [lintegral_one, measure_univ]
  | succ n ih =>
      have hrw : ∀ ω : ℕ → Fin k × ℝ,
          expWeight μvec a lam (banditTrajPrefix k (n + 1) ω)
            = expWeight μvec a lam (banditTrajPrefix k n ω) *
              (if (ω n).1 = a then
                ENNReal.ofReal (Real.exp (lam * ((ω n).2 - μvec a) - lam ^ 2 / 2)) else 1) :=
        expWeight_succ μvec a lam n
      simp only [hrw]
      rw [lintegral_mul_expTilt' μvec pol n a lam (expWeight μvec a lam)
        (measurable_expWeight μvec a lam n)]
      exact ih

end BanditAlgorithm



/-!
# The Chernoff bound for a Gaussian bandit

Markov's inequality applied to the exponential martingale of `ExpMartingale`:
for every arm `a`, every `λ` and every round `n`,

  `P( λ (S_a(n) − T_a(n) μ_a) − λ² T_a(n)/2 ≥ x ) ≤ e^{−x}`.

This is the fixed-`λ` deviation bound; optimising over `λ` at a fixed pull count
gives the usual `exp(−T_a d²/2)` sub-Gaussian tail, and mixing over `λ` gives the
self-normalised, uniform-in-time bound that
`chernoff_pairwise_selfnormalised_deviation_bound` asks for.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-- The exponent of the bandit exponential martingale. -/
noncomputable def expExponent (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) : ℝ :=
  lam * (trajRewardSum a n ω - (trajPullCount a n ω : ℝ) * μvec a)
    - lam ^ 2 * (trajPullCount a n ω : ℝ) / 2

theorem measurable_expWeight_traj (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) (n : ℕ) :
    Measurable fun ω : ℕ → Fin k × ℝ ↦ expWeight μvec a lam (banditTrajPrefix k n ω) :=
  (measurable_expWeight μvec a lam n).comp measurable_banditTrajPrefix

theorem expWeight_prefix_eq (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) :
    expWeight μvec a lam (banditTrajPrefix k n ω)
      = ENNReal.ofReal (Real.exp (expExponent μvec a lam n ω)) := by
  unfold expWeight expExponent
  rw [histPullCount_prefix, histRewardSum_prefix]

/-- **The Chernoff bound.** -/
theorem bandit_chernoff_aux (μvec : Fin k → ℝ) (pol : BanditPolicy k) (a : Fin k)
    (lam : ℝ) (n : ℕ) (x : ℝ) :
    banditTrajMeasure (gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | x ≤ expExponent μvec a lam n ω}
      ≤ ENNReal.ofReal (Real.exp (-x)) := by
  set P : Measure (ℕ → Fin k × ℝ) := banditTrajMeasure (gaussianBandit μvec) pol with hP
  set f : (ℕ → Fin k × ℝ) → ℝ≥0∞ := fun ω ↦ expWeight μvec a lam (banditTrajPrefix k n ω)
    with hf
  have hfmeas : Measurable f := measurable_expWeight_traj μvec a lam n
  have hint : ∫⁻ ω, f ω ∂P = 1 := lintegral_expWeight μvec pol a lam n
  -- the event is contained in a level set of `f`
  have hsub : {ω : ℕ → Fin k × ℝ | x ≤ expExponent μvec a lam n ω}
      ⊆ {ω : ℕ → Fin k × ℝ | ENNReal.ofReal (Real.exp x) ≤ f ω} := by
    intro ω hω
    show ENNReal.ofReal (Real.exp x) ≤ expWeight μvec a lam (banditTrajPrefix k n ω)
    rw [expWeight_prefix_eq]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hω)
  refine le_trans (measure_mono hsub) ?_
  -- Markov
  have hne : ENNReal.ofReal (Real.exp x) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos x
  have htop : ENNReal.ofReal (Real.exp x) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmarkov := meas_ge_le_lintegral_div (μ := P) hfmeas.aemeasurable hne htop
  rw [hint] at hmarkov
  refine le_trans hmarkov (le_of_eq ?_)
  rw [one_div, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos x), ← Real.exp_neg]

/-- The sub-Gaussian form: optimising the Chernoff bound is not needed for the
statement, but the bound at a fixed `λ` already gives the classical estimate. -/
theorem bandit_chernoff_aux' (μvec : Fin k → ℝ) (pol : BanditPolicy k) (a : Fin k)
    (lam : ℝ) (n : ℕ) (x : ℝ) :
    banditTrajMeasure (gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ |
          x + lam ^ 2 * (trajPullCount a n ω : ℝ) / 2
            ≤ lam * (trajRewardSum a n ω - (trajPullCount a n ω : ℝ) * μvec a)}
      ≤ ENNReal.ofReal (Real.exp (-x)) := by
  refine le_trans (measure_mono ?_) (bandit_chernoff_aux μvec pol a lam n x)
  intro ω hω
  simp only [Set.mem_setOf_eq, expExponent] at hω ⊢
  linarith

end BanditAlgorithm


open scoped Classical in
theorem _root_.solution {k : ℕ} (μvec : Fin k → ℝ)
    (pol : BanditAlgorithm.BanditPolicy k) (a : Fin k) (lam : ℝ) (n : ℕ) (x : ℝ) :
    BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ |
          x ≤ lam * ((∑ s ∈ (Finset.range n).filter fun s ↦ (ω s).1 = a, (ω s).2)
              - (BanditAlgorithm.trajPullCount a n ω : ℝ) * μvec a)
            - lam ^ 2 * (BanditAlgorithm.trajPullCount a n ω : ℝ) / 2}
      ≤ ENNReal.ofReal (Real.exp (-x)) :=
  BanditAlgorithm.bandit_chernoff_aux μvec pol a lam n x
