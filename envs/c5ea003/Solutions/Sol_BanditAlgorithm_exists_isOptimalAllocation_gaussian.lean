-- Prove2me | solution 1 for BanditAlgorithm.exists_isOptimalAllocation_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T19:52:31.45771+00:00
-- url     : https://prove2.me/submissions/c03e9f72-a0f4-4b6d-88c3-197ea2013bd5

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit


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
# The pooled-mean decomposition

The algebraic identity behind the closed form of the Track-and-Stop statistic
`Z_t` (L&S p. 409).  For weights `p, q ≥ 0` with `p + q > 0` and reals `u, v`,

  `p (u − m)² + q (v − m)² = (p + q)(m − m*)² + pq/(p+q) · (u − v)²`,

where `m* = (pu + qv)/(p + q)` is the pooled mean.  Consequently the left-hand
side is minimised at `m = m*`, with minimum value `pq/(p+q) · (u − v)²`.

In the Gaussian bandit this is exactly the statement that

  `inf_{m} [T_a · D(μ̂_a, m) + T_b · D(μ̂_b, m)] = ½ · T_a T_b/(T_a + T_b) · (μ̂_a − μ̂_b)²`,

since `D(x, m) = (x − m)²/2` for unit-variance Gaussians: the generalised
likelihood ratio for "arm `a` is not better than arm `b`" collapses to the closed
form used by `trajPairGLR`.
-/

namespace BanditAlgorithm

/-- **Pooled-mean decomposition.** -/
theorem weighted_sq_dist_decomp {p q u v m : ℝ} (hpq : p + q ≠ 0) :
    p * (u - m) ^ 2 + q * (v - m) ^ 2
      = (p + q) * (m - (p * u + q * v) / (p + q)) ^ 2 + p * q / (p + q) * (u - v) ^ 2 := by
  field_simp
  ring

/-- The pooled mean minimises the weighted sum of squared distances. -/
theorem pq_mul_sq_sub_le {p q u v m : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q) :
    p * q / (p + q) * (u - v) ^ 2 ≤ p * (u - m) ^ 2 + q * (v - m) ^ 2 := by
  rw [weighted_sq_dist_decomp hpq.ne']
  have : 0 ≤ (p + q) * (m - (p * u + q * v) / (p + q)) ^ 2 :=
    mul_nonneg hpq.le (sq_nonneg _)
  linarith

/-- Equality is attained at the pooled mean. -/
theorem pq_mul_sq_sub_eq {p q u v : ℝ} (hpq : p + q ≠ 0) :
    p * (u - (p * u + q * v) / (p + q)) ^ 2 + q * (v - (p * u + q * v) / (p + q)) ^ 2
      = p * q / (p + q) * (u - v) ^ 2 := by
  rw [weighted_sq_dist_decomp hpq]
  simp

/-- The minimum over `m` of the weighted sum of squared distances is exactly the
pooled term. -/
theorem iInf_weighted_sq_dist {p q u v : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q) :
    ⨅ m : ℝ, (p * (u - m) ^ 2 + q * (v - m) ^ 2) = p * q / (p + q) * (u - v) ^ 2 := by
  have hbdd : BddBelow (Set.range fun m : ℝ ↦ p * (u - m) ^ 2 + q * (v - m) ^ 2) :=
    ⟨p * q / (p + q) * (u - v) ^ 2, by
      rintro _ ⟨m, rfl⟩
      exact pq_mul_sq_sub_le hp hq hpq⟩
  refine le_antisymm ?_ (le_ciInf fun m ↦ pq_mul_sq_sub_le hp hq hpq)
  exact le_of_le_of_eq (ciInf_le hbdd ((p * u + q * v) / (p + q))) (pq_mul_sq_sub_eq hpq.ne')

/-- Half the pooled term, in the form used by `trajPairGLR`. -/
theorem half_pq_mul_sq_sub_le {p q u v m : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q) :
    p * q / (p + q) * (u - v) ^ 2 / 2
      ≤ p * ((u - m) ^ 2 / 2) + q * ((v - m) ^ 2 / 2) := by
  have h := pq_mul_sq_sub_le hp hq hpq (u := u) (v := v) (m := m)
  linarith

end BanditAlgorithm



/-!
# The Gaussian bandit class `𝓔^k_𝒩(1)`, explicitly

Everything the fixed-confidence analysis needs about `gaussianBandit μ`, made
computable:

* `banditArmMean_gaussianBandit` — the arm means are the parameters;
* `banditOptimalMean_gaussianBandit`, `banditOptimalArms_gaussianBandit` — the
  optimal value and the optimal-arm set are the maximum and the argmax of `μ`;
* `klDiv_gaussianBandit` — `D(ν_i ‖ ν'_i) = (μ_i − μ'_i)²/2`;
* `baiAlternatives_gaussianBandit` — membership in `𝓔_alt(ν)` is a condition on
  the parameter vectors only;
* `baiComplexity_inner_gaussianBandit` — the inner sum defining `c*(ν)⁻¹` is
  `∑_i α_i (μ_i − μ'_i)²/2`.

The last three are what turn the abstract characteristic time of L&S Eq. (33.4)
into the quantity Track-and-Stop actually tracks, and `pooled_pair_glr` is the
bridge to the closed form `trajPairGLR` used by `trajGLR`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. Means, optimal value, optimal arms -/

@[simp]
theorem banditArmMean_gaussianBandit (μvec : Fin k → ℝ) (i : Fin k) :
    banditArmMean (gaussianBandit μvec) i = μvec i := by
  simp [banditArmMean, gaussianBandit, integral_id_gaussianReal]

@[simp]
theorem banditOptimalMean_gaussianBandit (μvec : Fin k → ℝ) :
    banditOptimalMean (gaussianBandit μvec) = ⨆ i, μvec i := by
  simp [banditOptimalMean]

@[simp]
theorem banditGap_gaussianBandit (μvec : Fin k → ℝ) (i : Fin k) :
    banditGap (gaussianBandit μvec) i = (⨆ j, μvec j) - μvec i := by
  simp [banditGap]

theorem banditOptimalArms_gaussianBandit (μvec : Fin k → ℝ) :
    banditOptimalArms (gaussianBandit μvec) = {i | μvec i = ⨆ j, μvec j} := by
  ext i
  simp [banditOptimalArms]

/-- With finitely many arms and at least one, the optimal mean is attained. -/
theorem exists_mem_banditOptimalArms [NeZero k] (μvec : Fin k → ℝ) :
    ∃ i, i ∈ banditOptimalArms (gaussianBandit μvec) := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k)) μvec
    Finset.univ_nonempty
  refine ⟨i, ?_⟩
  rw [banditOptimalArms_gaussianBandit]
  refine le_antisymm (le_ciSup (f := μvec) (Finite.bddAbove_range _) i) ?_
  exact ciSup_le fun j ↦ hi j (Finset.mem_univ j)

/-- An arm is optimal exactly when it maximises the parameter vector. -/
theorem mem_banditOptimalArms_gaussianBandit_iff [NeZero k] (μvec : Fin k → ℝ) (i : Fin k) :
    i ∈ banditOptimalArms (gaussianBandit μvec) ↔ ∀ j, μvec j ≤ μvec i := by
  rw [banditOptimalArms_gaussianBandit]
  constructor
  · intro hi j
    rw [Set.mem_setOf_eq] at hi
    exact hi ▸ le_ciSup (f := μvec) (Finite.bddAbove_range _) j
  · intro hi
    exact le_antisymm (le_ciSup (f := μvec) (Finite.bddAbove_range _) i) (ciSup_le hi)

/-- The gap is positive exactly when the arm is not optimal. -/
theorem banditGap_pos_iff [NeZero k] (μvec : Fin k → ℝ) (i : Fin k) :
    0 < banditGap (gaussianBandit μvec) i ↔ ∃ j, μvec i < μvec j := by
  rw [banditGap_gaussianBandit, sub_pos]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    exact absurd (ciSup_le hcon) (not_le.mpr h)
  · rintro ⟨j, hj⟩
    exact lt_of_lt_of_le hj (le_ciSup (f := μvec) (Finite.bddAbove_range _) j)

/-! ## 2. Divergences -/

@[simp]
theorem klDiv_gaussianBandit (a b : Fin k → ℝ) (i : Fin k) :
    klDiv ((gaussianBandit a).P i) ((gaussianBandit b).P i)
      = ENNReal.ofReal ((a i - b i) ^ 2 / 2) := by
  simpa [gaussianBandit] using klDiv_gaussianReal_one (a i) (b i)

/-- The inner sum in the definition of the characteristic time, for Gaussians. -/
theorem baiComplexity_inner_gaussianBandit (a b : Fin k → ℝ) (α : Fin k → ℝ≥0) :
    (∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit a).P i) ((gaussianBandit b).P i))
      = ∑ i, (α i : ℝ≥0∞) * ENNReal.ofReal ((a i - b i) ^ 2 / 2) := by
  simp

/-- The alternative set of a Gaussian bandit inside the Gaussian class, in terms
of the parameter vectors. -/
theorem mem_baiAlternatives_gaussianBandit_iff (a : Fin k → ℝ)
    (ν' : StochasticBandit k) :
    ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit a) ↔
      ∃ b : Fin k → ℝ, ν' = gaussianBandit b ∧
        Disjoint (banditOptimalArms (gaussianBandit b))
          (banditOptimalArms (gaussianBandit a)) := by
  constructor
  · rintro ⟨⟨b, rfl⟩, hdisj⟩
    exact ⟨b, rfl, hdisj⟩
  · rintro ⟨b, rfl, hdisj⟩
    exact ⟨⟨b, rfl⟩, hdisj⟩

/-! ## 3. The bridge to the closed-form pair statistic -/

/-- **The Gaussian generalised likelihood ratio for a pair of arms.**  For weights
`p, q ≥ 0` (the pull counts) the least total divergence achievable by moving both
empirical means to a common value `m` is exactly the closed form used by
`trajPairGLR`. -/
theorem pooled_pair_glr {p q u w : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q) :
    ⨅ m : ℝ, (p * ((u - m) ^ 2 / 2) + q * ((w - m) ^ 2 / 2))
      = p * q / (p + q) * (u - w) ^ 2 / 2 := by
  have hbdd : BddBelow (Set.range fun m : ℝ ↦ p * ((u - m) ^ 2 / 2) + q * ((w - m) ^ 2 / 2)) :=
    ⟨p * q / (p + q) * (u - w) ^ 2 / 2, by
      rintro _ ⟨m, rfl⟩
      exact half_pq_mul_sq_sub_le hp hq hpq⟩
  refine le_antisymm ?_ (le_ciInf fun m ↦ half_pq_mul_sq_sub_le hp hq hpq)
  refine le_of_le_of_eq (ciInf_le hbdd ((p * u + q * w) / (p + q))) ?_
  have h := pq_mul_sq_sub_eq (p := p) (q := q) (u := u) (v := w) hpq.ne'
  linarith

/-- The pair statistic of `Def_TrackAndStop` is the Gaussian GLR of the pair. -/
theorem trajPairGLR_eq_iInf (a b : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ)
    (h : 0 < (trajPullCount a t ω : ℝ) + (trajPullCount b t ω : ℝ)) :
    trajPairGLR a b t ω
      = ⨅ m : ℝ, ((trajPullCount a t ω : ℝ) * ((trajEmpiricalMean a t ω - m) ^ 2 / 2)
          + (trajPullCount b t ω : ℝ) * ((trajEmpiricalMean b t ω - m) ^ 2 / 2)) := by
  rw [pooled_pair_glr (Nat.cast_nonneg _) (Nat.cast_nonneg _) h]
  rfl

end BanditAlgorithm



/-!
# The characteristic time of a Gaussian bandit, in closed form

For a Gaussian bandit `ν = ν_μ` with a *unique* best arm `i*` and an allocation
`α` with all weights positive, the inner infimum defining `c*(ν)⁻¹` in
L&S Eq. (33.4) is

  `⨅_{ν' ∈ 𝓔_alt(ν)} ∑_i α_i D(ν_i ‖ ν'_i)
      = min_{j ≠ i*} ½ · α_{i*} α_j / (α_{i*} + α_j) · (μ_{i*} − μ_j)²`.

This is *the* formula of the fixed-confidence literature (Garivier–Kaufmann,
COLT 2016, Eq. (3); L&S Eq. (33.4) specialised to `𝓔^k_𝒩(1)`), and it is what
turns the abstract characteristic time into something an algorithm can track.

Both halves come from the pooled-mean decomposition:

* **Lower bound.**  An alternative must make some arm `j ≠ i*` at least as good
  as `i*`, i.e. `μ'_{i*} ≤ μ'_j`.  Writing `a = μ_{i*} − μ'_{i*}` and
  `b = μ'_j − μ_j`, Cauchy–Schwarz gives
  `p a² + q b² ≥ pq/(p+q) (a + b)²`, and `a + b ≥ μ_{i*} − μ_j ≥ 0`.
* **Upper bound.**  Push `μ_{i*}` down to `m − η` and `μ_j` up to `m + η`, where
  `m` is the pooled mean, leaving every other arm alone.  The resulting bandit is
  a legitimate alternative for every `η > 0`, and its cost exceeds the pooled
  value by `2η pq(μ_{i*} − μ_j)/(p+q) + (p+q)η²/2`, which tends to `0`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. The two real-analytic cores -/

/-- **Lower bound.**  If the alternative reverses the order of the pair, its cost
is at least the pooled value. -/
theorem pooled_le_of_crossed {p q u v x y : ℝ} (hp : 0 < p) (hq : 0 < q)
    (huv : v ≤ u) (hxy : x ≤ y) :
    p * q / (p + q) * (u - v) ^ 2 / 2 ≤ p * ((u - x) ^ 2 / 2) + q * ((v - y) ^ 2 / 2) := by
  have hpq : 0 < p + q := by linarith
  set a : ℝ := u - x with ha
  set b : ℝ := y - v with hb
  have hab : u - v ≤ a + b := by simp only [ha, hb]; linarith
  have huv0 : 0 ≤ u - v := by linarith
  -- Cauchy-Schwarz: `p a² + q b² ≥ pq/(p+q) (a+b)²`
  have hcs : p * q / (p + q) * (a + b) ^ 2 ≤ p * a ^ 2 + q * b ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpq]
    nlinarith [sq_nonneg (q * b - p * a), sq_nonneg (a - b)]
  have hsq : (u - v) ^ 2 ≤ (a + b) ^ 2 := by nlinarith
  have hyv : (v - y) ^ 2 = b ^ 2 := by simp only [hb]; ring
  calc p * q / (p + q) * (u - v) ^ 2 / 2
      ≤ p * q / (p + q) * (a + b) ^ 2 / 2 := by
        have hcoef : 0 ≤ p * q / (p + q) := by positivity
        have := mul_le_mul_of_nonneg_left hsq hcoef
        linarith
    _ ≤ (p * a ^ 2 + q * b ^ 2) / 2 := by linarith
    _ = p * ((u - x) ^ 2 / 2) + q * ((v - y) ^ 2 / 2) := by
        rw [hyv]; simp only [ha]; ring

/-- **Upper bound, exact form.**  Splitting the pair symmetrically around the
pooled mean by `η` costs the pooled value plus an explicit `O(η)` term. -/
theorem cost_of_symmetric_split {p q u v η : ℝ} (hpq : p + q ≠ 0) :
    p * ((u - ((p * u + q * v) / (p + q) - η)) ^ 2 / 2)
        + q * ((v - ((p * u + q * v) / (p + q) + η)) ^ 2 / 2)
      = p * q / (p + q) * (u - v) ^ 2 / 2
        + 2 * η * (p * q * (u - v) / (p + q)) + (p + q) * η ^ 2 / 2 := by
  field_simp
  ring

/-! ## 2. The optimal-arm set of a bandit with a unique best arm -/

theorem banditOptimalArms_eq_singleton [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) :
    banditOptimalArms (gaussianBandit μvec) = {istar} := by
  ext i
  rw [mem_banditOptimalArms_gaussianBandit_iff]
  constructor
  · intro hi
    by_contra hne
    exact absurd (hi istar) (not_le.mpr (hstar i hne))
  · intro hi j
    rw [Set.mem_singleton_iff] at hi
    rw [hi]
    rcases eq_or_ne j istar with rfl | hj
    · exact le_rfl
    · exact (hstar j hj).le

/-- Under a unique best arm, being an alternative just means demoting `i*`. -/
theorem mem_baiAlternatives_iff_of_unique [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) (b : Fin k → ℝ) :
    gaussianBandit b ∈ baiAlternatives (Set.range (gaussianBandit (k := k)))
        (gaussianBandit μvec) ↔ ∃ j, b istar < b j := by
  rw [baiAlternatives, Set.mem_setOf_eq, banditOptimalArms_eq_singleton hstar]
  constructor
  · rintro ⟨-, hdisj⟩
    have hnot : istar ∉ banditOptimalArms (gaussianBandit b) := by
      intro hmem
      exact (Set.disjoint_left.mp hdisj hmem) rfl
    rw [mem_banditOptimalArms_gaussianBandit_iff] at hnot
    push_neg at hnot
    obtain ⟨j, hj⟩ := hnot
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨⟨b, rfl⟩, ?_⟩
    rw [Set.disjoint_right]
    rintro i rfl
    rw [mem_banditOptimalArms_gaussianBandit_iff]
    intro hcon
    exact absurd (hcon j) (not_le.mpr hj)

/-! ## 3. The formula -/

/-- The pooled cost of the pair `(i*, j)` under the allocation `α`. -/
noncomputable def pairCost (α : Fin k → ℝ≥0) (μvec : Fin k → ℝ) (istar j : Fin k) : ℝ :=
  (α istar : ℝ) * (α j : ℝ) / ((α istar : ℝ) + (α j : ℝ))
    * (μvec istar - μvec j) ^ 2 / 2

/-- **Lower bound half of the closed form.** -/
theorem le_inner_of_alternative [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {α : Fin k → ℝ≥0}
    (hα : ∀ i, 0 < α i) {b : Fin k → ℝ} (hb : ∃ j, b istar < b j) :
    (⨅ j ∈ {j : Fin k | j ≠ istar}, ENNReal.ofReal (pairCost α μvec istar j))
      ≤ ∑ i, (α i : ℝ≥0∞) * ENNReal.ofReal ((μvec i - b i) ^ 2 / 2) := by
  classical
  obtain ⟨j, hj⟩ := hb
  have hjne : j ≠ istar := by
    rintro rfl
    exact absurd hj (lt_irrefl _)
  have hp : (0 : ℝ) < (α istar : ℝ) := by exact_mod_cast hα istar
  have hq : (0 : ℝ) < (α j : ℝ) := by exact_mod_cast hα j
  -- the cost of the two relevant arms already exceeds the pooled value
  have hcore : ENNReal.ofReal (pairCost α μvec istar j)
      ≤ (α istar : ℝ≥0∞) * ENNReal.ofReal ((μvec istar - b istar) ^ 2 / 2)
        + (α j : ℝ≥0∞) * ENNReal.ofReal ((μvec j - b j) ^ 2 / 2) := by
    have hreal : pairCost α μvec istar j
        ≤ (α istar : ℝ) * ((μvec istar - b istar) ^ 2 / 2)
          + (α j : ℝ) * ((μvec j - b j) ^ 2 / 2) :=
      pooled_le_of_crossed hp hq (hstar j hjne).le hj.le
    calc ENNReal.ofReal (pairCost α μvec istar j)
        ≤ ENNReal.ofReal ((α istar : ℝ) * ((μvec istar - b istar) ^ 2 / 2)
            + (α j : ℝ) * ((μvec j - b j) ^ 2 / 2)) := ENNReal.ofReal_le_ofReal hreal
      _ = (α istar : ℝ≥0∞) * ENNReal.ofReal ((μvec istar - b istar) ^ 2 / 2)
            + (α j : ℝ≥0∞) * ENNReal.ofReal ((μvec j - b j) ^ 2 / 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (le_of_lt hp), ENNReal.ofReal_mul (le_of_lt hq),
            ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  refine le_trans (iInf_le_of_le j (iInf_le _ hjne)) (le_trans hcore ?_)
  -- and the full sum is at least the two-term sum
  have hsub : ({istar, j} : Finset (Fin k)) ⊆ Finset.univ := Finset.subset_univ _
  have hpair : (α istar : ℝ≥0∞) * ENNReal.ofReal ((μvec istar - b istar) ^ 2 / 2)
      + (α j : ℝ≥0∞) * ENNReal.ofReal ((μvec j - b j) ^ 2 / 2)
      = ∑ i ∈ ({istar, j} : Finset (Fin k)),
          (α i : ℝ≥0∞) * ENNReal.ofReal ((μvec i - b i) ^ 2 / 2) := by
    rw [Finset.sum_pair (Ne.symm hjne)]
  rw [hpair]
  exact Finset.sum_le_sum_of_subset hsub

/-! ## 4. Upper bound: the symmetric split is an admissible alternative -/

/-- The alternative that pushes `i*` and `j` symmetrically past each other. -/
noncomputable def splitVec (α : Fin k → ℝ≥0) (μvec : Fin k → ℝ) (istar j : Fin k)
    (η : ℝ) : Fin k → ℝ := fun l ↦
  if l = istar then
    ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j) / ((α istar : ℝ) + (α j : ℝ)) - η
  else if l = j then
    ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j) / ((α istar : ℝ) + (α j : ℝ)) + η
  else μvec l

/-- The error incurred by the symmetric split. -/
noncomputable def splitError (α : Fin k → ℝ≥0) (μvec : Fin k → ℝ) (istar j : Fin k)
    (η : ℝ) : ℝ :=
  2 * η * ((α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j) / ((α istar : ℝ) + (α j : ℝ)))
    + ((α istar : ℝ) + (α j : ℝ)) * η ^ 2 / 2

theorem splitError_nonneg {α : Fin k → ℝ≥0} {μvec : Fin k → ℝ} {istar j : Fin k} {η : ℝ}
    (hη : 0 ≤ η) (huv : μvec j ≤ μvec istar) : 0 ≤ splitError α μvec istar j η := by
  unfold splitError
  have h1 : 0 ≤ (α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
      / ((α istar : ℝ) + (α j : ℝ)) := by
    apply div_nonneg _ (by positivity)
    have : 0 ≤ μvec istar - μvec j := by linarith
    positivity
  have h2 : 0 ≤ ((α istar : ℝ) + (α j : ℝ)) * η ^ 2 / 2 := by positivity
  have h3 : 0 ≤ 2 * η * ((α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
      / ((α istar : ℝ) + (α j : ℝ))) := by positivity
  linarith

theorem splitError_le {α : Fin k → ℝ≥0} {μvec : Fin k → ℝ} {istar j : Fin k} {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (huv : μvec j ≤ μvec istar) :
    splitError α μvec istar j η
      ≤ η * (2 * ((α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
          / ((α istar : ℝ) + (α j : ℝ))) + ((α istar : ℝ) + (α j : ℝ)) / 2) := by
  unfold splitError
  have hC : 0 ≤ (α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
      / ((α istar : ℝ) + (α j : ℝ)) := by
    apply div_nonneg _ (by positivity)
    have : 0 ≤ μvec istar - μvec j := by linarith
    positivity
  have hsq : η ^ 2 ≤ η := by nlinarith
  have hpq : (0 : ℝ) ≤ (α istar : ℝ) + (α j : ℝ) := by positivity
  nlinarith

/-- The cost of the split alternative, exactly. -/
theorem sum_cost_splitVec {α : Fin k → ℝ≥0} {μvec : Fin k → ℝ} {istar j : Fin k}
    (hj : j ≠ istar) (hα : ∀ i, 0 < α i) (η : ℝ) (hη : 0 ≤ η)
    (huv : μvec j ≤ μvec istar) :
    (∑ i, (α i : ℝ≥0∞) *
        ENNReal.ofReal ((μvec i - splitVec α μvec istar j η i) ^ 2 / 2))
      = ENNReal.ofReal (pairCost α μvec istar j + splitError α μvec istar j η) := by
  classical
  have hp : (0 : ℝ) < (α istar : ℝ) := by exact_mod_cast hα istar
  have hq : (0 : ℝ) < (α j : ℝ) := by exact_mod_cast hα j
  have hpq : (α istar : ℝ) + (α j : ℝ) ≠ 0 := by positivity
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      i ∉ ({istar, j} : Finset (Fin k)) →
      (α i : ℝ≥0∞) * ENNReal.ofReal ((μvec i - splitVec α μvec istar j η i) ^ 2 / 2) = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    simp [splitVec, hi.1, hi.2]
  rw [← Finset.sum_subset (Finset.subset_univ ({istar, j} : Finset (Fin k))) hzero,
    Finset.sum_pair (Ne.symm hj)]
  have hi1 : splitVec α μvec istar j η istar
      = ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j)
          / ((α istar : ℝ) + (α j : ℝ)) - η := by simp [splitVec]
  have hi2 : splitVec α μvec istar j η j
      = ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j)
          / ((α istar : ℝ) + (α j : ℝ)) + η := by simp [splitVec, hj]
  rw [hi1, hi2]
  set m : ℝ := ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j)
      / ((α istar : ℝ) + (α j : ℝ)) with hm
  set A : ℝ := (μvec istar - (m - η)) ^ 2 / 2 with hA
  set B : ℝ := (μvec j - (m + η)) ^ 2 / 2 with hB
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hlhs : (α istar : ℝ≥0∞) * ENNReal.ofReal A + (α j : ℝ≥0∞) * ENNReal.ofReal B
      = ENNReal.ofReal ((α istar : ℝ) * A + (α j : ℝ) * B) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul hp.le, ENNReal.ofReal_mul hq.le,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  rw [hlhs]
  congr 1
  have hsplit := cost_of_symmetric_split (p := (α istar : ℝ)) (q := (α j : ℝ))
    (u := μvec istar) (v := μvec j) (η := η) hpq
  rw [hA, hB, hm, hsplit]
  unfold pairCost splitError
  ring

theorem pairCost_nonneg {α : Fin k → ℝ≥0} {μvec : Fin k → ℝ} (istar j : Fin k) :
    0 ≤ pairCost α μvec istar j := by
  unfold pairCost
  positivity

/-! ## 5. The closed form -/

/-- **The characteristic-time formula for a Gaussian bandit.**  For an allocation
with strictly positive weights and a bandit with a unique best arm, the inner
infimum of L&S Eq. (33.4) is the minimum over the competing arms of the pooled
pair cost. -/
theorem inner_gaussian_eq [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {α : Fin k → ℝ≥0} (hα : ∀ i, 0 < α i) :
    (⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
        ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i) (ν'.P i))
      = ⨅ j ∈ {j : Fin k | j ≠ istar}, ENNReal.ofReal (pairCost α μvec istar j) := by
  classical
  refine le_antisymm ?_ ?_
  · -- every competing arm gives an admissible alternative, up to `η`
    refine le_iInf₂ fun j hj ↦ ?_
    have hjne : j ≠ istar := hj
    have hp : (0 : ℝ) < (α istar : ℝ) := by exact_mod_cast hα istar
    have hq : (0 : ℝ) < (α j : ℝ) := by exact_mod_cast hα j
    set C : ℝ := 2 * ((α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
        / ((α istar : ℝ) + (α j : ℝ))) + ((α istar : ℝ) + (α j : ℝ)) / 2 with hCdef
    have hC : 0 < C := by
      have h1 : 0 ≤ 2 * ((α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
          / ((α istar : ℝ) + (α j : ℝ))) := by
        have : 0 ≤ μvec istar - μvec j := by linarith [hstar j hjne]
        apply mul_nonneg (by norm_num)
        apply div_nonneg _ (by positivity)
        positivity
      have h2 : 0 < ((α istar : ℝ) + (α j : ℝ)) / 2 := by positivity
      rw [hCdef]; linarith
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    set η : ℝ := min 1 ((ε : ℝ) / C) with hηdef
    have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have hη0 : 0 < η := lt_min one_pos (div_pos hεR hC)
    have hη1 : η ≤ 1 := min_le_left _ _
    have hserr : splitError α μvec istar j η ≤ (ε : ℝ) := by
      calc splitError α μvec istar j η ≤ η * C :=
            splitError_le hη0 hη1 (hstar j hjne).le
        _ ≤ ((ε : ℝ) / C) * C := by
            exact mul_le_mul_of_nonneg_right (min_le_right _ _) hC.le
        _ = (ε : ℝ) := by field_simp
    have hmem : gaussianBandit (splitVec α μvec istar j η)
        ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec) := by
      rw [mem_baiAlternatives_iff_of_unique hstar]
      refine ⟨j, ?_⟩
      have h1 : splitVec α μvec istar j η istar
          = ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j)
              / ((α istar : ℝ) + (α j : ℝ)) - η := by simp [splitVec]
      have h2 : splitVec α μvec istar j η j
          = ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j)
              / ((α istar : ℝ) + (α j : ℝ)) + η := by simp [splitVec, hjne]
      rw [h1, h2]; linarith
    calc (⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
            ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i) (ν'.P i))
        ≤ ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i)
            ((gaussianBandit (splitVec α μvec istar j η)).P i) :=
          iInf₂_le _ hmem
      _ = ∑ i, (α i : ℝ≥0∞) *
            ENNReal.ofReal ((μvec i - splitVec α μvec istar j η i) ^ 2 / 2) := by
          simp
      _ = ENNReal.ofReal (pairCost α μvec istar j + splitError α μvec istar j η) :=
          sum_cost_splitVec hjne hα η hη0.le (hstar j hjne).le
      _ = ENNReal.ofReal (pairCost α μvec istar j)
            + ENNReal.ofReal (splitError α μvec istar j η) :=
          ENNReal.ofReal_add (pairCost_nonneg _ _)
            (splitError_nonneg hη0.le (hstar j hjne).le)
      _ ≤ ENNReal.ofReal (pairCost α μvec istar j) + (ε : ℝ≥0∞) := by
          gcongr
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal hserr
  · -- every alternative costs at least the pooled minimum
    refine le_iInf₂ fun ν' hν' ↦ ?_
    obtain ⟨b, rfl⟩ : ∃ b : Fin k → ℝ, gaussianBandit b = ν' := hν'.1
    have hb : ∃ l, b istar < b l := (mem_baiAlternatives_iff_of_unique hstar b).mp hν'
    have hrw : (∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i)
        ((gaussianBandit b).P i))
        = ∑ i, (α i : ℝ≥0∞) * ENNReal.ofReal ((μvec i - b i) ^ 2 / 2) := by simp
    rw [hrw]
    exact le_inner_of_alternative hstar hα hb

end BanditAlgorithm



/-!
# The characteristic time of a Gaussian bandit is finite, with an explicit bound

Plugging the *uniform* allocation into the closed form of
`gaussian_bai_characteristic_time_formula` gives

  `c*(ν)⁻¹ ≥ min_{j ≠ i*} Δ_j² / (4k)`,   i.e.   `c*(ν) ≤ 4k / Δ_min²`.

Finiteness is not a technicality: L&S Theorem 33.6 and its lower half both speak
of `c*(ν).toReal`, and `ℝ≥0∞`-to-`ℝ` coercion silently sends `∞` to `0`, so
without `c*(ν) ≠ ∞` the statement of the theorem would be about the wrong
quantity.  The bound `4k/Δ_min²` is the familiar "the harder the gaps, the longer
it takes" scaling, and matches the `H₂`-style complexities of the fixed-budget
chapters.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-- The uniform allocation. -/
noncomputable def uniformAllocation (k : ℕ) : Fin k → ℝ≥0 := fun _ ↦ (k : ℝ≥0)⁻¹

theorem uniformAllocation_pos (hk : 0 < k) (i : Fin k) : 0 < uniformAllocation k i := by
  have : (0 : ℝ≥0) < (k : ℝ≥0) := by exact_mod_cast hk
  simpa [uniformAllocation] using this

theorem sum_uniformAllocation (hk : 0 < k) : ∑ i, uniformAllocation k i = 1 := by
  have hkne : (k : ℝ≥0) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact hk.ne'
  simp only [uniformAllocation, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact mul_inv_cancel₀ hkne

/-- The pair cost of the uniform allocation. -/
theorem pairCost_uniformAllocation (hk : 0 < k) (μvec : Fin k → ℝ) (istar j : Fin k) :
    pairCost (uniformAllocation k) μvec istar j
      = (μvec istar - μvec j) ^ 2 / (4 * (k : ℝ)) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  unfold pairCost uniformAllocation
  have hcast : (((k : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) = ((k : ℝ))⁻¹ := by
    simp
  rw [hcast]
  field_simp
  ring

/-- **The characteristic time is finite.**  Any positive lower bound on the gaps
gives an explicit bound on `c*(ν)`. -/
theorem baiComplexity_le_of_gap_le [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ j, j ≠ istar → Δ ≤ μvec istar - μvec j) :
    baiComplexity (gaussianBandit μvec) (Set.range (gaussianBandit (k := k)))
      ≤ ENNReal.ofReal (4 * (k : ℝ) / Δ ^ 2) := by
  classical
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  -- the uniform allocation already achieves `Δ²/(4k)`
  have hval : ENNReal.ofReal (Δ ^ 2 / (4 * (k : ℝ)))
      ≤ ⨅ j ∈ {j : Fin k | j ≠ istar},
          ENNReal.ofReal (pairCost (uniformAllocation k) μvec istar j) := by
    refine le_iInf₂ fun j hj ↦ ?_
    rw [pairCost_uniformAllocation hk]
    refine ENNReal.ofReal_le_ofReal ?_
    have hgj : Δ ≤ μvec istar - μvec j := hgap j hj
    have : Δ ^ 2 ≤ (μvec istar - μvec j) ^ 2 := by nlinarith
    exact div_le_div_of_nonneg_right this (by positivity) |>.trans_eq rfl
  have hformula := inner_gaussian_eq hstar (uniformAllocation_pos hk)
  have hle : ENNReal.ofReal (Δ ^ 2 / (4 * (k : ℝ)))
      ≤ ⨆ α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1},
          ⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
            ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i) (ν'.P i) := by
    refine le_trans (le_trans hval (le_of_eq hformula.symm)) ?_
    exact le_iSup₂ (f := fun α (_ : α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1}) ↦
      ⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
        ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i) (ν'.P i))
      (uniformAllocation k) (sum_uniformAllocation hk)
  rw [baiComplexity]
  refine le_trans (ENNReal.inv_le_inv.mpr hle) (le_of_eq ?_)
  rw [← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  field_simp

/-- **Finiteness of the characteristic time.** -/
theorem baiComplexity_ne_top [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) :
    baiComplexity (gaussianBandit μvec) (Set.range (gaussianBandit (k := k))) ≠ ⊤ := by
  classical
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  by_cases hk1 : ∀ j : Fin k, j = istar
  · -- a single arm: the alternative set is empty, so the infimum is `∞` and `c* = 0`
    have hempty : baiAlternatives (Set.range (gaussianBandit (k := k)))
        (gaussianBandit μvec) = ∅ := by
      ext ν'
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro hν'
      obtain ⟨b, rfl⟩ : ∃ b : Fin k → ℝ, gaussianBandit b = ν' := hν'.1
      obtain ⟨j, hj⟩ := (mem_baiAlternatives_iff_of_unique hstar b).mp hν'
      rw [hk1 j] at hj
      exact absurd hj (lt_irrefl _)
    have : baiComplexity (gaussianBandit μvec) (Set.range (gaussianBandit (k := k))) = 0 := by
      rw [baiComplexity]
      have htop : (⨆ α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1},
          ⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
            ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i) (ν'.P i)) = ⊤ := by
        refine le_antisymm le_top ?_
        refine le_iSup₂_of_le (uniformAllocation k) (sum_uniformAllocation hk) ?_
        rw [hempty]
        simp
      rw [htop, ENNReal.inv_top]
    rw [this]
    exact ENNReal.zero_ne_top
  · -- at least two arms: use the explicit bound with the smallest gap
    push_neg at hk1
    obtain ⟨j₀, hj₀⟩ := hk1
    set S : Finset (Fin k) := Finset.univ.filter (fun j ↦ j ≠ istar) with hS
    have hSne : S.Nonempty := ⟨j₀, by simp [hS, hj₀]⟩
    set Δ : ℝ := S.inf' hSne (fun j ↦ μvec istar - μvec j) with hΔdef
    have hΔ : 0 < Δ := by
      rw [hΔdef, Finset.lt_inf'_iff]
      intro j hj
      have : j ≠ istar := by simpa [hS] using hj
      linarith [hstar j this]
    have hgap : ∀ j, j ≠ istar → Δ ≤ μvec istar - μvec j := by
      intro j hj
      exact Finset.inf'_le _ (by simp [hS, hj])
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (baiComplexity_le_of_gap_le hstar hΔ hgap)

end BanditAlgorithm



/-!
# Existence of an optimal allocation

L&S Eq. (33.4) defines `c*(ν)⁻¹` as a *supremum* over the simplex.  Track-and-Stop
needs that supremum to be *attained*: the sampling rule tracks a maximiser `α*`.
This file supplies the maximiser for the Gaussian class.

The argument is the standard one, made possible by the closed form
`gaussian_bai_characteristic_time_formula`:

* the objective `α ↦ min_{j ≠ i*} α_{i*} α_j/(α_{i*} + α_j) · Δ_j²/2` is continuous
  on the whole of `Fin k → ℝ≥0` — the only delicate point is the origin of a pair,
  where the squeeze `0 ≤ pq/(p+q) ≤ p` applies;
* the simplex is compact, being a closed subset of the box `[0,1]^k`;
* so the maximum is attained, and the maximiser has full support because the
  objective vanishes as soon as one coordinate does, while the uniform allocation
  already achieves a strictly positive value.

Full support is exactly what lets the closed form be applied at the maximiser, so
the maximiser of the *closed form* is a maximiser of the original `ℝ≥0∞`-valued
objective.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. Continuity of the pair fraction -/

/-- `p q / (p + q)` is bounded by `p` on the nonnegative quadrant. -/
theorem pairFrac_le (p q : ℝ≥0) : (p : ℝ) * q / ((p : ℝ) + q) ≤ (p : ℝ) := by
  rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ (p : ℝ) + q) with h | h
  · rw [← h]; simp
  · rw [div_le_iff₀ h]
    nlinarith [q.coe_nonneg, p.coe_nonneg]

theorem pairFrac_nonneg (p q : ℝ≥0) : 0 ≤ (p : ℝ) * q / ((p : ℝ) + q) := by positivity

/-- The pair fraction is continuous on `ℝ≥0 × ℝ≥0`. -/
theorem continuous_pairFrac :
    Continuous fun x : ℝ≥0 × ℝ≥0 ↦ (x.1 : ℝ) * x.2 / ((x.1 : ℝ) + x.2) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ (x.1 : ℝ) + x.2) with h | h
  · -- both coordinates vanish: squeeze between `0` and the first coordinate
    have hx1 : (x.1 : ℝ) = 0 := by
      have h1 : (0 : ℝ) ≤ (x.1 : ℝ) := x.1.coe_nonneg
      have h2 : (0 : ℝ) ≤ (x.2 : ℝ) := x.2.coe_nonneg
      linarith
    have hval : (x.1 : ℝ) * x.2 / ((x.1 : ℝ) + x.2) = 0 := by rw [hx1]; simp
    rw [ContinuousAt, hval]
    refine squeeze_zero' (Filter.Eventually.of_forall fun y ↦ pairFrac_nonneg y.1 y.2)
      (Filter.Eventually.of_forall fun y ↦ pairFrac_le y.1 y.2) ?_
    have : Filter.Tendsto (fun y : ℝ≥0 × ℝ≥0 ↦ ((y.1 : ℝ))) (nhds x) (nhds ((x.1 : ℝ))) :=
      (NNReal.continuous_coe.comp continuous_fst).continuousAt
    rw [hx1] at this
    exact this
  · -- the denominator is nonzero
    refine ContinuousAt.div ?_ ?_ (ne_of_gt h)
    · exact ((NNReal.continuous_coe.comp continuous_fst).mul
        (NNReal.continuous_coe.comp continuous_snd)).continuousAt
    · exact ((NNReal.continuous_coe.comp continuous_fst).add
        (NNReal.continuous_coe.comp continuous_snd)).continuousAt

/-- `pairCost` is continuous in the allocation. -/
theorem continuous_pairCost (μvec : Fin k → ℝ) (istar j : Fin k) :
    Continuous fun α : Fin k → ℝ≥0 ↦ pairCost α μvec istar j := by
  unfold pairCost
  have hpair : Continuous fun α : Fin k → ℝ≥0 ↦ ((α istar, α j) : ℝ≥0 × ℝ≥0) :=
    (continuous_apply istar).prodMk (continuous_apply j)
  have h : Continuous fun α : Fin k → ℝ≥0 ↦
      ((α istar : ℝ) * (α j : ℝ) / ((α istar : ℝ) + (α j : ℝ))) :=
    continuous_pairFrac.comp hpair
  exact ((h.mul continuous_const).div_const 2)

/-! ## 2. Compactness of the simplex -/

theorem isCompact_simplex (k : ℕ) :
    IsCompact {α : Fin k → ℝ≥0 | ∑ i, α i = 1} := by
  have hclosed : IsClosed {α : Fin k → ℝ≥0 | ∑ i, α i = 1} := by
    have hcont : Continuous fun α : Fin k → ℝ≥0 ↦ ∑ i, α i :=
      continuous_finset_sum _ fun i _ ↦ continuous_apply i
    exact isClosed_eq hcont continuous_const
  have hsub : {α : Fin k → ℝ≥0 | ∑ i, α i = 1} ⊆ Set.Icc (0 : Fin k → ℝ≥0) 1 := by
    intro α hα
    refine ⟨fun i ↦ zero_le', fun i ↦ ?_⟩
    have : α i ≤ ∑ j, α j := Finset.single_le_sum (fun j _ ↦ zero_le') (Finset.mem_univ i)
    rw [hα] at this
    exact this
  exact IsCompact.of_isClosed_subset (isCompact_Icc) hclosed hsub

theorem simplex_nonempty (hk : 0 < k) :
    {α : Fin k → ℝ≥0 | ∑ i, α i = 1}.Nonempty :=
  ⟨uniformAllocation k, sum_uniformAllocation hk⟩

/-! ## 3. The maximiser -/

/-- The closed-form objective: the smallest pooled pair cost among the competing
arms.  With `Finset.inf'` this needs the competing set to be nonempty, i.e. `k ≥ 2`. -/
noncomputable def allocObjective (μvec : Fin k → ℝ) (istar : Fin k)
    (hne : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty)
    (α : Fin k → ℝ≥0) : ℝ :=
  (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).inf' hne fun j ↦ pairCost α μvec istar j

theorem continuous_allocObjective (μvec : Fin k → ℝ) (istar : Fin k)
    (hne : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty) :
    Continuous (allocObjective μvec istar hne) := by
  rw [continuous_iff_continuousAt]
  intro α
  unfold allocObjective ContinuousAt
  exact Filter.Tendsto.finset_inf'_nhds_apply hne fun j _ ↦
    (continuous_pairCost μvec istar j).continuousAt

/-- **A maximiser exists.** -/
theorem exists_max_allocObjective (hk : 0 < k) (μvec : Fin k → ℝ) (istar : Fin k)
    (hne : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty) :
    ∃ α₀ ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1},
      ∀ α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1},
        allocObjective μvec istar hne α ≤ allocObjective μvec istar hne α₀ := by
  obtain ⟨α₀, hα₀, hmax⟩ := (isCompact_simplex k).exists_isMaxOn (simplex_nonempty hk)
    (continuous_allocObjective μvec istar hne).continuousOn
  exact ⟨α₀, hα₀, fun α hα ↦ hmax hα⟩

/-! ## 4. The maximiser has full support -/

theorem allocObjective_uniform_pos (hk : 0 < k) {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hne : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty) :
    0 < allocObjective μvec istar hne (uniformAllocation k) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [allocObjective, Finset.lt_inf'_iff]
  intro j hj
  have hjne : j ≠ istar := by simpa using hj
  rw [pairCost_uniformAllocation hk]
  have hgap : 0 < μvec istar - μvec j := by linarith [hstar j hjne]
  positivity

theorem pairCost_eq_zero_of_coord_eq_zero {α : Fin k → ℝ≥0} {μvec : Fin k → ℝ}
    {istar j : Fin k} (h : α istar = 0 ∨ α j = 0) :
    pairCost α μvec istar j = 0 := by
  unfold pairCost
  rcases h with h | h <;> simp [h]

/-- A maximiser of the objective has all coordinates positive. -/
theorem pos_of_isMax (hk : 0 < k) {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hne : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty)
    {α₀ : Fin k → ℝ≥0} (hα₀ : ∑ i, α₀ i = 1)
    (hmax : ∀ α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1},
      allocObjective μvec istar hne α ≤ allocObjective μvec istar hne α₀) :
    ∀ i, 0 < α₀ i := by
  have hpos : 0 < allocObjective μvec istar hne α₀ :=
    lt_of_lt_of_le (allocObjective_uniform_pos hk hstar hne)
      (hmax _ (sum_uniformAllocation hk))
  intro i
  rcases eq_or_lt_of_le (zero_le' : (0 : ℝ≥0) ≤ α₀ i) with h | h
  · exfalso
    -- a vanishing coordinate makes some pair cost vanish
    rcases eq_or_ne i istar with hi | hi
    · obtain ⟨j, hj⟩ := id hne
      have hle : allocObjective μvec istar hne α₀ ≤ pairCost α₀ μvec istar j :=
        Finset.inf'_le _ hj
      rw [pairCost_eq_zero_of_coord_eq_zero (Or.inl (hi ▸ h.symm))] at hle
      linarith
    · have hmem : i ∈ Finset.univ.filter fun j : Fin k ↦ j ≠ istar := by simp [hi]
      have hle : allocObjective μvec istar hne α₀ ≤ pairCost α₀ μvec istar i :=
        Finset.inf'_le _ hmem
      rw [pairCost_eq_zero_of_coord_eq_zero (Or.inr h.symm)] at hle
      linarith
  · exact h

/-! ## 5. Degenerate allocations cost nothing -/

/-- An `ℝ≥0∞` infimum of `ofReal`s over a nonempty finite set is the `ofReal` of the
`Finset.inf'`. -/
theorem iInf_ofReal_eq_ofReal_inf' {S : Finset (Fin k)} (hne : S.Nonempty)
    (f : Fin k → ℝ) (hf : ∀ j ∈ S, 0 ≤ f j) :
    (⨅ j ∈ (↑S : Set (Fin k)), ENNReal.ofReal (f j)) = ENNReal.ofReal (S.inf' hne f) := by
  refine le_antisymm ?_ (le_iInf₂ fun j hj ↦ ENNReal.ofReal_le_ofReal (Finset.inf'_le _ hj))
  obtain ⟨j₀, hj₀S, hj₀⟩ := Finset.exists_mem_eq_inf' hne f
  exact le_trans (iInf_le_of_le j₀ (iInf_le _ hj₀S)) (le_of_eq (by rw [hj₀]))

/-- If some weight vanishes, the alternative set contains a bandit of zero cost. -/
theorem inner_eq_zero_of_coord_eq_zero [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {β : Fin k → ℝ≥0} {i : Fin k}
    (hi : β i = 0) (j₀ : Fin k) (hj₀ : j₀ ≠ istar) :
    (⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
        ∑ l, (β l : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P l) (ν'.P l)) = 0 := by
  classical
  refine le_antisymm ?_ bot_le
  set c : ℝ := if i = istar then μvec j₀ - 1 else μvec istar + 1 with hc
  set b : Fin k → ℝ := fun l ↦ if l = i then c else μvec l with hb
  have hbi : b i = c := by rw [hb]; simp
  have hbne : ∀ l, l ≠ i → b l = μvec l := by
    intro l hl; rw [hb]; simp [hl]
  have hmem : gaussianBandit b ∈ baiAlternatives
      (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec) := by
    rw [mem_baiAlternatives_iff_of_unique hstar]
    rcases eq_or_ne i istar with hii | hii
    · refine ⟨j₀, ?_⟩
      have hji : j₀ ≠ i := by rw [hii]; exact hj₀
      have h1 : b istar = μvec j₀ - 1 := by
        rw [← hii, hbi, hc, if_pos hii]
      have h2 : b j₀ = μvec j₀ := hbne j₀ hji
      rw [h1, h2]; linarith
    · refine ⟨i, ?_⟩
      have h1 : b istar = μvec istar := hbne istar (Ne.symm hii)
      have h2 : b i = μvec istar + 1 := by rw [hbi, hc, if_neg hii]
      rw [h1, h2]; linarith
  have hcost : (∑ l, (β l : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P l)
      ((gaussianBandit b).P l)) = 0 := by
    refine Finset.sum_eq_zero fun l _ ↦ ?_
    rcases eq_or_ne l i with rfl | hli
    · rw [hi]; simp
    · rw [klDiv_gaussianBandit, hbne l hli]; simp
  exact le_trans (iInf₂_le _ hmem) (le_of_eq hcost)

/-! ## 6. Existence of an optimal allocation -/

/-- **An optimal allocation exists, and it has full support.** -/
theorem exists_isOptimalAllocation [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) :
    ∃ α : Fin k → ℝ≥0, (∀ i, 0 < α i) ∧
      IsOptimalAllocation (gaussianBandit μvec)
        (Set.range (gaussianBandit (k := k))) α := by
  classical
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  set S : Finset (Fin k) := Finset.univ.filter (fun j : Fin k ↦ j ≠ istar) with hS
  have hinv : (baiComplexity (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))))⁻¹
      = ⨆ α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1},
          ⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k)))
              (gaussianBandit μvec),
            ∑ l, (α l : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P l) (ν'.P l) := by
    rw [baiComplexity, inv_inv]
  rcases S.eq_empty_or_nonempty with hSe | hne
  · refine ⟨uniformAllocation k, uniformAllocation_pos hk, sum_uniformAllocation hk, ?_⟩
    have hempty : baiAlternatives (Set.range (gaussianBandit (k := k)))
        (gaussianBandit μvec) = ∅ := by
      ext ν'
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro hν'
      obtain ⟨c, rfl⟩ : ∃ c : Fin k → ℝ, gaussianBandit c = ν' := hν'.1
      obtain ⟨j, hj⟩ := (mem_baiAlternatives_iff_of_unique hstar c).mp hν'
      have hjs : j = istar := by
        by_contra hcon
        have hmemS : j ∈ S := by simp [hS, hcon]
        rw [hSe] at hmemS
        exact absurd hmemS (Finset.notMem_empty j)
      rw [hjs] at hj
      exact absurd hj (lt_irrefl _)
    rw [hinv, hempty]
    simp only [Set.mem_empty_iff_false, iInf_false, iInf_top]
    symm
    refine le_antisymm le_top ?_
    exact le_iSup₂_of_le (f := fun (α : Fin k → ℝ≥0)
      (_ : α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1}) ↦ (⊤ : ℝ≥0∞))
      (uniformAllocation k) (sum_uniformAllocation hk) le_rfl
  · obtain ⟨j₀, hj₀mem⟩ := id hne
    have hj₀ne : j₀ ≠ istar := by simpa [hS] using hj₀mem
    obtain ⟨α₀, hα₀mem, hα₀max⟩ := exists_max_allocObjective hk μvec istar hne
    have hα₀sum : ∑ i, α₀ i = 1 := hα₀mem
    have hα₀pos := pos_of_isMax hk hstar hne hα₀sum hα₀max
    have hFfull : ∀ α : Fin k → ℝ≥0, (∀ i, 0 < α i) →
        (⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k)))
            (gaussianBandit μvec),
          ∑ l, (α l : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P l) (ν'.P l))
          = ENNReal.ofReal (allocObjective μvec istar hne α) := by
      intro α hα
      rw [inner_gaussian_eq hstar hα]
      have hsets : {j : Fin k | j ≠ istar} = (↑S : Set (Fin k)) := by
        ext j; simp [hS]
      rw [hsets]
      exact iInf_ofReal_eq_ofReal_inf' hne _ fun j _ ↦ pairCost_nonneg _ _
    refine ⟨α₀, hα₀pos, hα₀sum, ?_⟩
    rw [hinv]
    refine le_antisymm (le_iSup₂ (f := fun (α : Fin k → ℝ≥0)
      (_ : α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1}) ↦
        ⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
          ∑ l, (α l : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P l) (ν'.P l))
      α₀ hα₀mem) ?_
    refine iSup₂_le fun β hβ ↦ ?_
    by_cases hfull : ∀ i, 0 < β i
    · rw [hFfull β hfull, hFfull α₀ hα₀pos]
      exact ENNReal.ofReal_le_ofReal (hα₀max β hβ)
    · push_neg at hfull
      obtain ⟨i, hi⟩ := hfull
      have hzero : β i = 0 := le_antisymm hi zero_le'
      rw [inner_eq_zero_of_coord_eq_zero hstar hzero j₀ hj₀ne]
      exact bot_le

end BanditAlgorithm


theorem _root_.solution {k : ℕ} [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) :
    ∃ α : Fin k → NNReal, (∀ i, 0 < α i) ∧
      BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit μvec)
        (Set.range (BanditAlgorithm.gaussianBandit (k := k))) α :=
  BanditAlgorithm.exists_isOptimalAllocation hstar
