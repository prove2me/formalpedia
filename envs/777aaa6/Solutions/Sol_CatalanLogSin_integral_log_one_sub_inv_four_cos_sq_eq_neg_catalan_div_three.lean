-- Prove2me | solution 1 for CatalanLogSin.integral_log_one_sub_inv_four_cos_sq_eq_neg_catalan_div_three
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T16:54:50.296014+00:00
-- url     : https://prove2.me/submissions/2f5c46bd-2b02-47b7-a218-eff8b9adeddf

import Mathlib

/-!
The log-sine integrals at `π/4` and `3π/4`, and `∫₀^{π/4} log (1 - 1/(4 cos²θ)) dθ = -G/3`,
`G` Catalan's constant. Verbatim the file `CatalanLogSin.lean` of the mission's source repository.
-/

set_option autoImplicit false

section CatalanLogSinFile

/-!
# The log-sine integral at `π/4` and Catalan's constant

Target: `∫ θ in 0..π/4, log (2 sin θ) = -G/2`, where `G = ∑ (-1)ⁿ/(2n+1)²` is
Catalan's constant. This is the analytic core of the covolume of the Picard group,
and Mathlib has nothing about Catalan's constant.

Route: the Taylor series of `log (1 - z)` on the open disk, integrated term by term
along the arc `θ ↦ r e^{2iθ}`, then `r → 1` by dominated convergence.
-/

open Real MeasureTheory intervalIntegral Filter Topology

namespace CatalanLogSin

/-- Catalan's constant. -/
noncomputable def catalan : ℝ := ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * n + 1) ^ 2

/-- The real part of the Taylor series of `-log (1 - z)`. -/
theorem hasSum_neg_log_norm {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (z ^ n).re / n) (-Real.log ‖1 - z‖) := by
  have h := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hz)
  have h1 : ∀ n : ℕ, ((z ^ n / n : ℂ)).re = (z ^ n).re / n := fun n =>
    Complex.div_natCast_re _ n
  have h2 : (-Complex.log (1 - z)).re = -Real.log ‖1 - z‖ := by
    simp [Complex.log_re]
  rw [← h2]
  simpa only [h1] using h

theorem re_ofReal_mul_exp (a ψ : ℝ) :
    ((a : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)).re = a * Real.cos ψ := by
  simp [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- Along the circle of radius `r`, the series is `∑ rⁿ cos(nφ)/n`. -/
theorem hasSum_neg_log_norm_circle {r : ℝ} (hr : |r| < 1) (φ : ℝ) :
    HasSum (fun n : ℕ => r ^ n * Real.cos (n * φ) / n)
      (-Real.log ‖1 - (r : ℂ) * Complex.exp (φ * Complex.I)‖) := by
  have hz : ‖(r : ℂ) * Complex.exp (φ * Complex.I)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hr
  have hpow : ∀ n : ℕ, ((r : ℂ) * Complex.exp (φ * Complex.I)) ^ n
      = ((r ^ n : ℝ) : ℂ) * Complex.exp (((n * φ : ℝ) : ℝ) * Complex.I) := by
    intro n
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hfun : (fun n : ℕ => r ^ n * Real.cos (n * φ) / n)
      = fun n : ℕ => (((r : ℂ) * Complex.exp (φ * Complex.I)) ^ n).re / n := by
    funext n
    rw [hpow n, re_ofReal_mul_exp]
  rw [hfun]
  exact hasSum_neg_log_norm hz

/-- The `n`-th term, integrated over the arc. -/
theorem integral_term (n : ℕ) (r : ℝ) :
    ∫ θ in (0:ℝ)..(π/4), r ^ n * Real.cos (n * (2 * θ)) / n
      = r ^ n * Real.sin (n * (π/2)) / (2 * n ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hcos : ∫ θ in (0:ℝ)..(π/4), Real.cos (n * (2 * θ)) = Real.sin (n * (π/2)) / (2 * n) := by
    have h : ∀ θ : ℝ, Real.cos (n * (2 * θ)) = Real.cos ((2 * n) * θ) := by
      intro θ; ring_nf
    simp_rw [h]
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) (by positivity : (2 * (n:ℝ)) ≠ 0)]
    rw [integral_cos]
    have : (2 * (n:ℝ)) * (π/4) = n * (π/2) := by ring
    rw [this]
    simp [smul_eq_mul]
    field_simp
  calc ∫ θ in (0:ℝ)..(π/4), r ^ n * Real.cos (n * (2 * θ)) / n
      = (r ^ n / n) * ∫ θ in (0:ℝ)..(π/4), Real.cos (n * (2 * θ)) := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        funext θ
        ring
    _ = r ^ n * Real.sin (n * (π/2)) / (2 * n ^ 2) := by
        rw [hcos]
        field_simp
        try ring


/-- Term-by-term integration along the arc, for a radius `r` inside the disk. -/
theorem integral_arc {r : ℝ} (hr : |r| < 1) :
    ∫ θ in (0:ℝ)..(π/4), (-Real.log ‖1 - (r : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖)
      = ∑' n : ℕ, r ^ n * Real.sin (n * (π/2)) / (2 * n ^ 2) := by
  have hpi : (0:ℝ) ≤ π/4 := by positivity
  have hcont : ∀ n : ℕ, Continuous fun θ : ℝ => r ^ n * Real.cos (n * (2 * θ)) / n := by
    intro n
    fun_prop
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun θ : ℝ => r ^ n * Real.cos (n * (2 * θ)) / n)
      (volume.restrict (Set.Ioc (0:ℝ) (π/4))) := fun n => (hcont n).aestronglyMeasurable
  -- the terms are dominated by a geometric series
  have hbound : ∀ n : ℕ, ∫⁻ θ in Set.Ioc (0:ℝ) (π/4),
      ‖r ^ n * Real.cos (n * (2 * θ)) / n‖ₑ ≤ ENNReal.ofReal (|r| ^ n * (π/4)) := by
    intro n
    have hle : ∀ θ : ℝ, ‖r ^ n * Real.cos (n * (2 * θ)) / n‖ₑ ≤ ENNReal.ofReal (|r| ^ n) := by
      intro θ
      rw [← ofReal_norm_eq_enorm]
      refine ENNReal.ofReal_le_ofReal ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      rw [norm_div, norm_mul]
      have h1 : ‖r ^ n‖ = |r| ^ n := by
        rw [Real.norm_eq_abs, abs_pow]
      have h2 : ‖Real.cos (n * (2 * θ))‖ ≤ 1 := by
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one _
      have h3 : (1:ℝ) ≤ ‖(n : ℝ)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
        exact hn1
      rw [h1]
      have hnum : |r| ^ n * ‖Real.cos (n * (2 * θ))‖ ≤ |r| ^ n :=
        (mul_le_mul_of_nonneg_left h2 (by positivity)).trans_eq (mul_one _)
      have hden : |r| ^ n * ‖Real.cos (n * (2 * θ))‖ / ‖(n : ℝ)‖
          ≤ |r| ^ n * ‖Real.cos (n * (2 * θ))‖ :=
        div_le_self (by positivity) h3
      linarith
    calc ∫⁻ θ in Set.Ioc (0:ℝ) (π/4), ‖r ^ n * Real.cos (n * (2 * θ)) / n‖ₑ
        ≤ ∫⁻ _ in Set.Ioc (0:ℝ) (π/4), ENNReal.ofReal (|r| ^ n) := lintegral_mono hle
      _ = ENNReal.ofReal (|r| ^ n) * volume (Set.Ioc (0:ℝ) (π/4)) := by
          rw [setLIntegral_const]
      _ = ENNReal.ofReal (|r| ^ n * (π/4)) := by
          rw [Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
  have hsummable : Summable fun n : ℕ => |r| ^ n * (π/4) :=
    (summable_geometric_of_lt_one (abs_nonneg r) hr).mul_right _
  have hfin : ∑' n : ℕ, ∫⁻ θ in Set.Ioc (0:ℝ) (π/4),
      ‖r ^ n * Real.cos (n * (2 * θ)) / n‖ₑ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsummable]
    exact ENNReal.ofReal_ne_top
  have hpt : ∀ θ : ℝ,
      (-Real.log ‖1 - (r : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖)
        = ∑' n : ℕ, r ^ n * Real.cos (n * (2 * θ)) / n := fun θ =>
    ((hasSum_neg_log_norm_circle hr (2 * θ)).tsum_eq).symm
  rw [intervalIntegral.integral_of_le hpi]
  simp_rw [hpt]
  rw [MeasureTheory.integral_tsum hmeas hfin]
  refine tsum_congr fun n => ?_
  have h := integral_term n r
  rw [intervalIntegral.integral_of_le hpi] at h
  exact h


/-- `‖1 - e^{2iθ}‖ = 2 sin θ` on `[0, π/2]`. -/
theorem norm_one_sub_exp {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π/2) :
    ‖1 - Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖ = 2 * Real.sin θ := by
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hB : 0 ≤ 2 * Real.sin θ := by positivity
  have hcos : Real.cos (2 * θ) = 1 - 2 * Real.sin θ ^ 2 := by
    have h := Real.cos_two_mul θ
    have h2 := Real.sin_sq_add_cos_sq θ
    nlinarith [h, h2]
  have hre : (Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)).re = Real.cos (2 * θ) :=
    Complex.exp_ofReal_mul_I_re _
  have him : (Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)).im = Real.sin (2 * θ) :=
    Complex.exp_ofReal_mul_I_im _
  have hsq : ‖1 - Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖ ^ 2 = (2 * Real.sin θ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, hre, him]
    nlinarith [Real.sin_sq_add_cos_sq (2 * θ), hcos]
  rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_sq hB]

theorem summable_catalan : Summable (fun n : ℕ => (-1 : ℝ) ^ n / (2 * n + 1) ^ 2) := by
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := summable_one_div_nat_pow.2 one_lt_two
    have h2 := (summable_nat_add_iff 1).2 h
    refine h2.congr fun n => ?_
    push_cast
    ring
  refine Summable.of_norm (hbase.of_nonneg_of_le (fun n => norm_nonneg _) fun n => ?_)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * (n:ℝ) + 1) ^ 2)]
  rw [div_le_div_iff_of_pos_left one_pos (by positivity) (by positivity)]
  nlinarith [hn]

/-- The series at radius one is Catalan's constant halved. -/
theorem hasSum_boundary :
    HasSum (fun n : ℕ => Real.sin (n * (π/2)) / (2 * n ^ 2)) (catalan / 2) := by
  have hc : HasSum (fun n : ℕ => (-1 : ℝ) ^ n / (2 * n + 1) ^ 2) catalan :=
    summable_catalan.hasSum
  have hhalf : HasSum (fun n : ℕ => ((-1 : ℝ) ^ n / (2 * n + 1) ^ 2) / 2) (catalan / 2) :=
    hc.div_const 2
  have hinj : Function.Injective (fun m : ℕ => 2 * m + 1) := by
    intro a b h
    simp only at h
    omega
  have hzero : ∀ n ∉ Set.range (fun m : ℕ => 2 * m + 1),
      Real.sin (n * (π/2)) / (2 * n ^ 2) = 0 := by
    intro n hn
    have heven : ∃ m : ℕ, n = 2 * m := by
      rcases Nat.even_or_odd n with he | ho
      · obtain ⟨m, hm⟩ := he
        exact ⟨m, by omega⟩
      · obtain ⟨m, hm⟩ := ho
        exact absurd (Set.mem_range.2 ⟨m, show 2 * m + 1 = n by omega⟩) hn
    obtain ⟨m, rfl⟩ := heven
    have harg : ((2 * m : ℕ) : ℝ) * (π/2) = m * π := by
      push_cast
      ring
    rw [harg, Real.sin_nat_mul_pi, zero_div]
  rw [← hinj.hasSum_iff hzero]
  have hfun : (fun m : ℕ => Real.sin ((((2 * m + 1 : ℕ)) : ℝ) * (π/2))
        / (2 * (((2 * m + 1 : ℕ)) : ℝ) ^ 2))
      = fun m : ℕ => ((-1 : ℝ) ^ m / (2 * m + 1) ^ 2) / 2 := by
    funext m
    have harg : (((2 * m + 1 : ℕ)) : ℝ) * (π/2) = m * π + π/2 := by
      push_cast
      ring
    have hcosm : Real.cos ((m : ℝ) * π) = (-1) ^ m := by
      have h := Real.cos_int_mul_pi (m : ℤ)
      push_cast at h
      simpa using h
    rw [harg, Real.sin_add, Real.sin_nat_mul_pi, Real.cos_pi_div_two, Real.sin_pi_div_two, hcosm]
    have hne : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  simp only [Function.comp_def]
  rw [hfun]
  exact hhalf

/-- The dominating bound: on the arc, `|log ‖1 - r e^{iφ}‖| ≤ log 2 + |log (sin φ)|`,
uniformly in `r ∈ [0, 1]`. The lower bound is `‖1 - r e^{iφ}‖² - sin²φ = (r - cos φ)²`. -/
theorem abs_log_norm_le {r φ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hsin : 0 < Real.sin φ) :
    |Real.log ‖1 - (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖|
      ≤ Real.log 2 + |Real.log (Real.sin φ)| := by
  have hsq : ‖1 - (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ ^ 2
      = 1 - 2 * r * Real.cos φ + r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have hnn : 0 ≤ ‖1 - (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ := norm_nonneg _
  have hge : Real.sin φ ≤ ‖1 - (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ := by
    nlinarith [hsq, sq_nonneg (r - Real.cos φ), Real.sin_sq_add_cos_sq φ, hsin, hnn]
  have hle : ‖1 - (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0, norm_one] at h
    linarith
  have hpos : 0 < ‖1 - (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ := lt_of_lt_of_le hsin hge
  have hlog_le : Real.log ‖1 - (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ ≤ Real.log 2 :=
    Real.log_le_log hpos hle
  have hlog_ge : Real.log (Real.sin φ)
      ≤ Real.log ‖1 - (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ := Real.log_le_log hsin hge
  have h2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  have habs : -|Real.log (Real.sin φ)| ≤ Real.log (Real.sin φ) := neg_abs_le _
  rw [abs_le]
  constructor <;> linarith [abs_nonneg (Real.log (Real.sin φ))]

/-- **The log-sine integral at `π/4`.** `∫₀^{π/4} log (2 sin θ) dθ = -G/2`. -/
theorem integral_log_two_sin :
    ∫ θ in (0:ℝ)..(π/4), Real.log (2 * Real.sin θ) = -(catalan / 2) := by
  have hpi4 : (0:ℝ) < π/4 := by positivity
  have hIoo : Set.Ioo (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) := Ioo_mem_nhdsLT (by norm_num)
  -- Abel's limit theorem on the series side
  have habel : Tendsto (fun r : ℝ => ∑' n : ℕ, (Real.sin (n * (π/2)) / (2 * n ^ 2)) * r ^ n)
      (𝓝[<] (1:ℝ)) (𝓝 (catalan / 2)) :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hasSum_boundary.tendsto_sum_nat
  -- inside the disk the integral is that series
  have hev : ∀ᶠ r : ℝ in 𝓝[<] (1:ℝ),
      (∫ θ in (0:ℝ)..(π/4),
          -Real.log ‖1 - (r:ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖)
        = ∑' n : ℕ, (Real.sin (n * (π/2)) / (2 * n ^ 2)) * r ^ n := by
    filter_upwards [hIoo] with r hr
    have habs : |r| < 1 := by
      rw [abs_of_pos hr.1]
      exact hr.2
    rw [integral_arc habs]
    exact tsum_congr fun n => by ring
  -- dominated convergence on the integral side
  have hdct : Tendsto (fun r : ℝ =>
      ∫ θ in (0:ℝ)..(π/4),
        -Real.log ‖1 - (r:ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖)
      (𝓝[<] (1:ℝ)) (𝓝 (∫ θ in (0:ℝ)..(π/4), -Real.log (2 * Real.sin θ))) := by
    have hsin2 : ∀ θ ∈ Set.uIoc (0:ℝ) (π/4), 0 < Real.sin (2 * θ) := by
      intro θ hθ
      rw [Set.uIoc_of_le hpi4.le] at hθ
      refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) ?_
      have := hθ.2
      have hpi := Real.pi_pos
      linarith
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun θ => Real.log 2 + |Real.log (Real.sin (2 * θ))|) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun r => ?_
      refine (Real.measurable_log.comp ?_).neg.aestronglyMeasurable
      refine (Continuous.norm ?_).measurable
      fun_prop
    · filter_upwards [hIoo] with r hr
      refine Eventually.of_forall fun θ hθ => ?_
      rw [Real.norm_eq_abs, abs_neg]
      have h2θ := hsin2 θ hθ
      have := abs_log_norm_le hr.1.le hr.2.le h2θ
      simpa using this
    · have hbase : IntervalIntegrable (Real.log ∘ Real.sin) volume 0 (π/2) :=
        intervalIntegrable_log_sin
      have hscale : IntervalIntegrable (fun x => (Real.log ∘ Real.sin) (2 * x)) volume
          (0 / 2) ((π/2) / 2) := hbase.comp_mul_left
      have hscale' : IntervalIntegrable (fun x => Real.log (Real.sin (2 * x))) volume 0 (π/4) := by
        have h0 : (0:ℝ) / 2 = 0 := by norm_num
        have h1 : (π/2) / 2 = π/4 := by ring
        rw [h0, h1] at hscale
        exact hscale
      exact intervalIntegrable_const.add hscale'.abs
    · refine Eventually.of_forall fun θ hθ => ?_
      have h2θ := hsin2 θ hθ
      have hθ' : θ ∈ Set.Ioc (0:ℝ) (π/4) := by rwa [Set.uIoc_of_le hpi4.le] at hθ
      have hne : ‖1 - Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖ ≠ 0 := by
        rw [norm_one_sub_exp hθ'.1.le (by linarith [hθ'.2, Real.pi_pos] : θ ≤ π/2)]
        have : 0 < Real.sin θ :=
          Real.sin_pos_of_pos_of_lt_pi hθ'.1 (by linarith [hθ'.2, Real.pi_pos])
        positivity
      have hcont : ContinuousAt
          (fun r : ℝ => -Real.log ‖1 - (r:ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖) 1 := by
        have hnorm : ContinuousAt
            (fun r : ℝ => ‖1 - (r:ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖) 1 :=
          (Continuous.norm (by fun_prop)).continuousAt
        exact (hnorm.log (by simpa using hne)).neg
      have hlim : Tendsto (fun r : ℝ =>
          -Real.log ‖1 - (r:ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖)
          (𝓝[<] (1:ℝ))
          (𝓝 (-Real.log ‖1 - ((1:ℝ):ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖)) :=
        hcont.tendsto.mono_left nhdsWithin_le_nhds
      have hval : -Real.log ‖1 - ((1:ℝ):ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖
          = -Real.log (2 * Real.sin θ) := by
        rw [Complex.ofReal_one, one_mul,
          norm_one_sub_exp hθ'.1.le (by linarith [hθ'.2, Real.pi_pos] : θ ≤ π/2)]
      rw [hval] at hlim
      exact hlim
  have habel' : Tendsto (fun r : ℝ =>
      ∫ θ in (0:ℝ)..(π/4),
        -Real.log ‖1 - (r:ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖)
      (𝓝[<] (1:ℝ)) (𝓝 (catalan / 2)) := habel.congr' (hev.mono fun r h => h.symm)
  have hlimit : (∫ θ in (0:ℝ)..(π/4), -Real.log (2 * Real.sin θ)) = catalan / 2 :=
    tendsto_nhds_unique hdct habel'
  rw [intervalIntegral.integral_neg] at hlimit
  linarith [hlimit]

/-! ### The log-sine integral at `3π/4`, and `∫₀^{π/4} log (1 - sec²θ/4) = -G/3`

The volume of the half box (see `Thurston23.lean`) is `-∫₀^{π/4} log (1 - 1/(4 cos²θ)) dθ`.
The identity `sin 3θ = sin θ (4 cos²θ - 1)` writes the integrand as
`log (2 sin 3θ) - log (2 sin 2θ) - log (2 cos θ)`, and each piece is a log-sine integral:
substituting, they are `⅓ ∫₀^{3π/4}`, `½ ∫₀^{π/2}` and `∫_{π/4}^{π/2}` of `log (2 sin u)`,
whose values `G/2`, `0`, `G/2` follow from the value at `π/4` above and Mathlib's value
at `π/2`. -/

/-- `log (2 sin u)` is interval integrable on any `[a, b] ⊆ [0, π)`. -/
theorem intervalIntegrable_log_two_sin {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < π) :
    IntervalIntegrable (fun u => Real.log (2 * Real.sin u)) volume a b := by
  have h1 : IntervalIntegrable (Real.log ∘ Real.sin) volume a b := intervalIntegrable_log_sin
  have h2 : IntervalIntegrable (fun u => Real.log 2 + (Real.log ∘ Real.sin) u) volume a b :=
    intervalIntegral.intervalIntegrable_const.add h1
  rw [intervalIntegrable_iff] at h2 ⊢
  refine h2.congr_fun (fun u hu => ?_) measurableSet_uIoc
  rw [Set.uIoc_of_le hab] at hu
  have hsin : 0 < Real.sin u :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hu.1]) (by linarith [hu.2])
  simp only [Function.comp_apply]
  rw [Real.log_mul two_ne_zero hsin.ne']

/-- `∫₀^{π/2} log (2 sin u) du = 0`, from Mathlib's value of `∫₀^{π/2} log (sin u)`. -/
theorem integral_log_two_sin_pi_div_two :
    ∫ u in (0:ℝ)..π/2, Real.log (2 * Real.sin u) = 0 := by
  have hpi := Real.pi_pos
  have h : ∫ u in (0:ℝ)..π/2, Real.log (2 * Real.sin u)
      = ∫ u in (0:ℝ)..π/2, (Real.log 2 + Real.log (Real.sin u)) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => ?_)
    rw [Set.uIoc_of_le (by positivity)] at hu
    have hsin : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu.1 (by linarith [hu.2])
    rw [Real.log_mul two_ne_zero hsin.ne']
  rw [h, intervalIntegral.integral_add (g := fun u => Real.log (Real.sin u))
    intervalIntegral.intervalIntegrable_const intervalIntegrable_log_sin,
    intervalIntegral.integral_const, integral_log_sin_zero_pi_div_two]
  simp only [smul_eq_mul, sub_zero]
  ring

/-- `∫_{π/4}^{π/2} log (2 sin u) du = G/2`. -/
theorem integral_log_two_sin_pi_div_four_pi_div_two :
    ∫ u in (π/4)..π/2, Real.log (2 * Real.sin u) = catalan / 2 := by
  have hpi := Real.pi_pos
  have h := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_log_two_sin (a := 0) (b := π/4) le_rfl (by positivity) (by linarith))
    (intervalIntegrable_log_two_sin (a := π/4) (b := π/2) (by positivity) (by linarith)
      (by linarith))
  rw [integral_log_two_sin, integral_log_two_sin_pi_div_two] at h
  linarith

/-- `∫_{π/2}^{3π/4} log (2 sin u) du = G/2`, by `u ↦ π - u`. -/
theorem integral_log_two_sin_pi_div_two_three_pi_div_four :
    ∫ u in (π/2)..3*π/4, Real.log (2 * Real.sin u) = catalan / 2 := by
  have h := intervalIntegral.integral_comp_sub_left (a := π/4) (b := π/2)
    (fun u => Real.log (2 * Real.sin u)) π
  rw [show π - π/2 = π/2 by ring, show π - π/4 = 3*π/4 by ring] at h
  rw [← h, ← integral_log_two_sin_pi_div_four_pi_div_two]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [Real.sin_pi_sub]

/-- **The log-sine integral at `3π/4`.** `∫₀^{3π/4} log (2 sin u) du = G/2`. -/
theorem integral_log_two_sin_three_pi_div_four :
    ∫ u in (0:ℝ)..3*π/4, Real.log (2 * Real.sin u) = catalan / 2 := by
  have hpi := Real.pi_pos
  have h := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_log_two_sin (a := 0) (b := π/2) le_rfl (by positivity) (by linarith))
    (intervalIntegrable_log_two_sin (a := π/2) (b := 3*π/4) (by positivity) (by linarith)
      (by linarith))
  rw [integral_log_two_sin_pi_div_two, integral_log_two_sin_pi_div_two_three_pi_div_four] at h
  linarith

/-- `∫₀^{π/4} log (2 sin 3θ) dθ = G/6`. -/
theorem integral_log_two_sin_three_mul :
    ∫ θ in (0:ℝ)..π/4, Real.log (2 * Real.sin (3 * θ)) = catalan / 6 := by
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := π/4)
    (fun u => Real.log (2 * Real.sin u)) (c := 3) (by norm_num)
  rw [show (3:ℝ) * 0 = 0 by ring, show (3:ℝ) * (π/4) = 3*π/4 by ring,
    integral_log_two_sin_three_pi_div_four] at h
  rw [h, smul_eq_mul]
  ring

/-- `∫₀^{π/4} log (2 sin 2θ) dθ = 0`. -/
theorem integral_log_two_sin_two_mul :
    ∫ θ in (0:ℝ)..π/4, Real.log (2 * Real.sin (2 * θ)) = 0 := by
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := π/4)
    (fun u => Real.log (2 * Real.sin u)) (c := 2) (by norm_num)
  rw [show (2:ℝ) * 0 = 0 by ring, show (2:ℝ) * (π/4) = π/2 by ring,
    integral_log_two_sin_pi_div_two] at h
  rw [h, smul_zero]

/-- `∫₀^{π/4} log (2 cos θ) dθ = G/2`, by `θ ↦ π/2 - θ`. -/
theorem integral_log_two_cos :
    ∫ θ in (0:ℝ)..π/4, Real.log (2 * Real.cos θ) = catalan / 2 := by
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := π/4)
    (fun u => Real.log (2 * Real.sin u)) (π/2)
  rw [sub_zero, show π/2 - π/4 = π/4 by ring, integral_log_two_sin_pi_div_four_pi_div_two] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [Real.sin_pi_div_two_sub]

/-- The trigonometric identity behind the box: for `0 < θ ≤ π/4`,
`1 - 1/(4 cos²θ) = 2 sin 3θ / (2 sin 2θ · 2 cos θ)`, so its logarithm splits. -/
theorem log_one_sub_inv_four_cos_sq {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ π/4) :
    Real.log (1 - 1 / (4 * Real.cos θ ^ 2))
      = Real.log (2 * Real.sin (3 * θ)) - Real.log (2 * Real.sin (2 * θ))
        - Real.log (2 * Real.cos θ) := by
  have hpi := Real.pi_pos
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hsin2 : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsin3 : 0 < Real.sin (3 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs := Real.sin_sq_add_cos_sq θ
  have h3 : Real.sin (3 * θ) = Real.sin θ * (4 * Real.cos θ ^ 2 - 1) := by
    rw [Real.sin_three_mul]
    linear_combination (-4 * Real.sin θ) * hs
  have hcne := hcos.ne'
  have hsne := hsin.ne'
  have key : 1 - 1 / (4 * Real.cos θ ^ 2)
      = (2 * Real.sin (3 * θ)) / ((2 * Real.sin (2 * θ)) * (2 * Real.cos θ)) := by
    rw [h3, Real.sin_two_mul]
    field_simp
    ring
  rw [key, Real.log_div (by positivity) (by positivity),
    Real.log_mul (x := 2 * Real.sin (2 * θ)) (y := 2 * Real.cos θ) (by positivity) (by positivity)]
  ring

/-- **`∫₀^{π/4} log (1 - 1/(4 cos²θ)) dθ = -G/3`.** Minus this is the volume of the
half box, so the covolume of the Picard group is `G/3`. -/
theorem integral_log_one_sub_inv_four_cos_sq :
    ∫ θ in (0:ℝ)..π/4, Real.log (1 - 1 / (4 * Real.cos θ ^ 2)) = -(catalan / 3) := by
  have hpi := Real.pi_pos
  have hI3 : IntervalIntegrable (fun θ => Real.log (2 * Real.sin (3 * θ))) volume 0 (π/4) := by
    have h : IntervalIntegrable (fun x => Real.log (2 * Real.sin (3 * x))) volume (0 / 3)
        ((3*π/4) / 3) :=
      (intervalIntegrable_log_two_sin (a := 0) (b := 3*π/4) le_rfl (by positivity)
        (by linarith)).comp_mul_left
    rw [show (0:ℝ) / 3 = 0 by ring, show (3*π/4) / 3 = π/4 by ring] at h
    exact h
  have hI2 : IntervalIntegrable (fun θ => Real.log (2 * Real.sin (2 * θ))) volume 0 (π/4) := by
    have h : IntervalIntegrable (fun x => Real.log (2 * Real.sin (2 * x))) volume (0 / 2)
        ((π/2) / 2) :=
      (intervalIntegrable_log_two_sin (a := 0) (b := π/2) le_rfl (by positivity)
        (by linarith)).comp_mul_left
    rw [show (0:ℝ) / 2 = 0 by ring, show (π/2) / 2 = π/4 by ring] at h
    exact h
  have hIc : IntervalIntegrable (fun θ => Real.log (2 * Real.cos θ)) volume 0 (π/4) := by
    have h : IntervalIntegrable (fun x => Real.log (2 * Real.sin (π/2 - x))) volume
        (π/2 - π/4) (π/2 - π/2) :=
      (intervalIntegrable_log_two_sin (a := π/4) (b := π/2) (by positivity) (by linarith)
        (by linarith)).comp_sub_left (π/2)
    rw [sub_self, show π/2 - π/4 = π/4 by ring] at h
    simpa only [Real.sin_pi_div_two_sub] using h.symm
  have hcongr : ∫ θ in (0:ℝ)..π/4, Real.log (1 - 1 / (4 * Real.cos θ ^ 2))
      = ∫ θ in (0:ℝ)..π/4, (Real.log (2 * Real.sin (3 * θ)) - Real.log (2 * Real.sin (2 * θ))
          - Real.log (2 * Real.cos θ)) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun θ hθ => ?_)
    rw [Set.uIoc_of_le (by positivity)] at hθ
    exact log_one_sub_inv_four_cos_sq hθ.1 hθ.2
  rw [hcongr, intervalIntegral.integral_sub (hI3.sub hI2) hIc, intervalIntegral.integral_sub hI3 hI2,
    integral_log_two_sin_three_mul, integral_log_two_sin_two_mul, integral_log_two_cos]
  ring


end CatalanLogSin

end CatalanLogSinFile

theorem solution :
    ∫ θ in (0:ℝ)..Real.pi / 4, Real.log (1 - 1 / (4 * Real.cos θ ^ 2))
      = -((∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) / 3) := by
  have h := CatalanLogSin.integral_log_one_sub_inv_four_cos_sq
  unfold CatalanLogSin.catalan at h
  exact h
