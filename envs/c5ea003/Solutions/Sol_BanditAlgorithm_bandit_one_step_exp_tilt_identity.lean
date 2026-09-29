-- Prove2me | solution 1 for BanditAlgorithm.bandit_one_step_exp_tilt_identity
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T20:15:44.561372+00:00
-- url     : https://prove2.me/submissions/17fcc7b7-1f58-411f-a528-20c2c4457795

import Theorems.Thm_BanditAlgorithm_banditTrajMeasure_joint_eq_compProd
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


theorem _root_.solution {k : ℕ} (μvec : Fin k → ℝ)
    (pol : BanditAlgorithm.BanditPolicy k) (n : ℕ) (a : Fin k) (lam : ℝ)
    (F : BanditAlgorithm.BanditHistory k n → ENNReal) (hF : Measurable F) :
    ∫⁻ ω, F (BanditAlgorithm.banditTrajPrefix k n ω) *
        (if (ω n).1 = a then
          ENNReal.ofReal (Real.exp (lam * ((ω n).2 - μvec a) - lam ^ 2 / 2)) else 1)
        ∂(BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol)
      = ∫⁻ ω, F (BanditAlgorithm.banditTrajPrefix k n ω)
        ∂(BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol) :=
  BanditAlgorithm.lintegral_mul_expTilt' μvec pol n a lam F hF
