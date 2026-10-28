-- Prove2me | solution 1 for HarmonicBuilding.weakly_subharmonic_mean_value_ineq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T07:35:20.702352+00:00
-- url     : https://prove2.me/submissions/b8effeab-92dd-48e4-9731-6c040d634b48

import Mathlib

/-! cd7f3207 C1-4 (i): radial cutoffs and their Laplacian. -/

open Set Filter Topology MeasureTheory intervalIntegral
open scoped ContDiff
set_option autoImplicit false

/-- The smooth step from `1` (for `x ≤ 0`) to `0` (for `x ≥ 1`). -/
noncomputable def cdPsi (x : ℝ) : ℝ := 1 - Real.smoothTransition x

theorem cdPsi_contDiff (n : ℕ∞) : ContDiff ℝ n cdPsi :=
  contDiff_const.sub Real.smoothTransition.contDiff

theorem cdPsi_of_nonpos {x : ℝ} (hx : x ≤ 0) : cdPsi x = 1 := by
  simp [cdPsi, Real.smoothTransition.zero_of_nonpos hx]

theorem cdPsi_of_one_le {x : ℝ} (hx : 1 ≤ x) : cdPsi x = 0 := by
  simp [cdPsi, Real.smoothTransition.one_of_one_le hx]

theorem cdPsi_mem (x : ℝ) : cdPsi x ∈ Icc (0 : ℝ) 1 := by
  unfold cdPsi
  constructor
  · linarith [Real.smoothTransition.le_one x]
  · linarith [Real.smoothTransition.nonneg x]

theorem cdPsi_deriv_contDiff : ContDiff ℝ ∞ (deriv cdPsi) :=
  (contDiff_infty_iff_deriv.1 (cdPsi_contDiff ⊤)).2

theorem cdPsi_deriv2_contDiff : ContDiff ℝ ∞ (deriv (deriv cdPsi)) :=
  (contDiff_infty_iff_deriv.1 cdPsi_deriv_contDiff).2

theorem cdPsi_facts :
    (∀ x, HasDerivAt cdPsi (deriv cdPsi x) x) ∧
    (∀ x, HasDerivAt (deriv cdPsi) (deriv (deriv cdPsi) x) x) ∧
    Continuous (deriv cdPsi) ∧ Continuous (deriv (deriv cdPsi)) ∧
    cdPsi 0 = 1 ∧ cdPsi 1 = 0 ∧ deriv cdPsi 0 = 0 ∧ deriv cdPsi 1 = 0 := by
  have hc1 : Continuous (deriv cdPsi) := cdPsi_deriv_contDiff.continuous
  have hloc0 : ∀ x : ℝ, x < 0 → deriv cdPsi x = 0 := by
    intro x hx
    have : cdPsi =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact cdPsi_of_nonpos (le_of_lt hy)
    rw [this.deriv_eq, deriv_const]
  have hloc1 : ∀ x : ℝ, 1 < x → deriv cdPsi x = 0 := by
    intro x hx
    have : cdPsi =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact cdPsi_of_one_le (le_of_lt hy)
    rw [this.deriv_eq, deriv_const]
  refine ⟨fun x => ((cdPsi_contDiff 1).differentiable (by norm_num) x).hasDerivAt,
    fun x => (cdPsi_deriv_contDiff.differentiable (by simp) x).hasDerivAt, hc1,
    cdPsi_deriv2_contDiff.continuous, cdPsi_of_nonpos le_rfl, cdPsi_of_one_le le_rfl, ?_, ?_⟩
  · have h1 : Tendsto (deriv cdPsi) (𝓝[<] 0) (𝓝 (deriv cdPsi 0)) :=
      hc1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (deriv cdPsi) (𝓝[<] 0) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hloc0 y hy).symm
    exact tendsto_nhds_unique h1 h2
  · have h1 : Tendsto (deriv cdPsi) (𝓝[>] 1) (𝓝 (deriv cdPsi 1)) :=
      hc1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (deriv cdPsi) (𝓝[>] 1) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hloc1 y hy).symm
    exact tendsto_nhds_unique h1 h2

/-- Laplacian of a radial function `Φ(‖w - c‖²)`. -/
theorem lap_radial (Φ : ℝ → ℝ) (hd : Differentiable ℝ Φ) (hdd : Differentiable ℝ (deriv Φ))
    (c z : ℂ) :
    Laplacian.laplacian (fun w => Φ (‖w - c‖ ^ 2)) z =
      4 * deriv Φ (‖z - c‖ ^ 2) + 4 * ‖z - c‖ ^ 2 * deriv (deriv Φ) (‖z - c‖ ^ 2) := by
  have hN : ∀ w : ℂ, HasFDerivAt (fun x : ℂ => ‖x - c‖ ^ 2)
      (2 • (innerSL ℝ (w - c)).comp (ContinuousLinearMap.id ℝ ℂ)) w := by
    intro w
    have := ((hasFDerivAt_id w).sub_const c).norm_sq
    simpa using this
  have hη : ∀ w : ℂ, HasFDerivAt (fun x : ℂ => Φ (‖x - c‖ ^ 2))
      ((2 * deriv Φ (‖w - c‖ ^ 2)) • innerSL ℝ (w - c)) w := by
    intro w
    have := (hd _).hasDerivAt.comp_hasFDerivAt w (hN w)
    convert this using 1
    ext v
    simp [smul_eq_mul]
    ring
  have hfd : fderiv ℝ (fun x : ℂ => Φ (‖x - c‖ ^ 2)) =
      fun w => (2 * deriv Φ (‖w - c‖ ^ 2)) • innerSL ℝ (w - c) := by
    funext w; exact (hη w).fderiv
  have ha : HasFDerivAt (fun w : ℂ => 2 * deriv Φ (‖w - c‖ ^ 2))
      (2 • (deriv (deriv Φ) (‖z - c‖ ^ 2) •
        (2 • (innerSL ℝ (z - c)).comp (ContinuousLinearMap.id ℝ ℂ)))) z := by
    have := ((hdd _).hasDerivAt.comp_hasFDerivAt z (hN z)).const_mul 2
    convert this using 1
    ext v; simp [smul_eq_mul]
  have hB : HasFDerivAt (fun w : ℂ => innerSL ℝ (w - c))
      ((innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ).comp (ContinuousLinearMap.id ℝ ℂ)) z :=
    (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c)
  have hL : HasFDerivAt (fun w : ℂ => (2 * deriv Φ (‖w - c‖ ^ 2)) • innerSL ℝ (w - c)) _ z :=
    ha.smul hB
  rw [show Laplacian.laplacian (fun w => Φ (‖w - c‖ ^ 2)) z =
      fderiv ℝ (fderiv ℝ (fun w => Φ (‖w - c‖ ^ 2))) z 1 1 +
      fderiv ℝ (fderiv ℝ (fun w => Φ (‖w - c‖ ^ 2))) z Complex.I Complex.I by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    simp [iteratedFDeriv_two_apply]]
  rw [hfd, hL.fderiv]
  have e : ‖z - c‖ ^ 2 = (z - c).re * (z - c).re + (z - c).im * (z - c).im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  simp [smul_eq_mul, Complex.inner]
  rw [e]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

theorem radPhi_contDiff {r h : ℝ} (hr : 0 < r) (hh : 0 < h) (n : ℕ∞) :
    ContDiff ℝ n (fun t : ℝ => cdPsi ((Real.sqrt t - r) / h)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t < r ^ 2
  · have : (fun t : ℝ => cdPsi ((Real.sqrt t - r) / h)) =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with y hy
      apply cdPsi_of_nonpos
      have : Real.sqrt y < r := (Real.sqrt_lt' hr).2 hy
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hh.le
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have ht0 : t ≠ 0 := by
      have : 0 < r ^ 2 := by positivity
      intro h0; rw [h0] at ht; exact ht this
    exact (cdPsi_contDiff n).contDiffAt.comp t
      (((Real.contDiffAt_sqrt ht0).sub contDiffAt_const).div_const h)

theorem radPhi_hasDerivAt {r h t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => cdPsi ((Real.sqrt t - r) / h))
      (deriv cdPsi ((Real.sqrt t - r) / h) * (1 / (2 * Real.sqrt t) / h)) t :=
  (cdPsi_facts.1 _).comp t (((Real.hasDerivAt_sqrt ht.ne').sub_const r).div_const h)

theorem radPhi_profile {r h s : ℝ} (hh : 0 < h) (hs : 0 < s) :
    4 * deriv (fun t : ℝ => cdPsi ((Real.sqrt t - r) / h)) (s ^ 2) +
      4 * s ^ 2 * deriv (deriv (fun t : ℝ => cdPsi ((Real.sqrt t - r) / h))) (s ^ 2) =
      deriv (deriv cdPsi) ((s - r) / h) / h ^ 2 + deriv cdPsi ((s - r) / h) / (h * s) := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hsq : Real.sqrt (s ^ 2) = s := Real.sqrt_sq hs.le
  set D : ℝ → ℝ := fun t => deriv cdPsi ((Real.sqrt t - r) / h) * (1 / (2 * Real.sqrt t) / h)
    with hD
  have hev : deriv (fun t : ℝ => cdPsi ((Real.sqrt t - r) / h)) =ᶠ[𝓝 (s ^ 2)] D := by
    filter_upwards [Ioi_mem_nhds hs2] with t ht
    exact (radPhi_hasDerivAt ht).deriv
  have hg := ((Real.hasDerivAt_sqrt hs2.ne').sub_const r).div_const h
  have p1 := (cdPsi_facts.2.1 ((Real.sqrt (s ^ 2) - r) / h)).comp (s ^ 2) hg
  have p2 := ((hasDerivAt_const (s ^ 2) (1 : ℝ)).div
    ((Real.hasDerivAt_sqrt hs2.ne').const_mul 2) (by positivity)).div_const h
  have hDd := p1.mul p2
  rw [hev.deriv_eq, (radPhi_hasDerivAt hs2).deriv]
  rw [show deriv D (s ^ 2) = _ from hDd.deriv]
  simp only [Function.comp_apply, Pi.div_apply, hsq]
  field_simp
  ring

/-- Polar-coordinates formula for a radial weight with support in `[0, R)`. -/
theorem polar_radial (c : ℂ) {R : ℝ} (hR : 0 < R) (g : ℂ → ℝ) (hg : Continuous g)
    (F : ℝ → ℝ) (hF : Continuous F) (hF0 : ∀ s, R ≤ s → F s = 0) :
    ∫ z, g z * F ‖z - c‖ = ∫ s in (0 : ℝ)..R, F s * (s * ∫ θ in (0 : ℝ)..2 * Real.pi,
      g (c + (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
  have h1 : ∫ z, g z * F ‖z - c‖ = ∫ w, g (c + w) * F ‖w‖ := by
    rw [← integral_add_left_eq_self (fun z => g z * F ‖z - c‖) c]
    simp
  rw [h1, ← Complex.integral_comp_polarCoord_symm]
  simp only [Complex.polarCoord_symm_apply, smul_eq_mul]
  set K : ℝ × ℝ → ℝ := fun p => p.1 * (g (c + (p.1 : ℂ) * ((Real.cos p.2 : ℂ) +
    (Real.sin p.2 : ℂ) * Complex.I)) * F |p.1|) with hK
  have hKc : Continuous K := by
    simp only [hK]
    fun_prop
  have hKint : IntegrableOn K (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
    have hc : IntegrableOn K (Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi) :=
      hKc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    refine hc.of_forall_diff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro ⟨s, θ⟩ ⟨⟨hs, hθ⟩, hn⟩
    simp only [mem_prod, mem_Icc, not_and_or, not_le] at hn hs hθ
    have hsR : R ≤ s := by
      rcases hn with (h | h) | (h | h)
      · exact absurd h (not_lt.2 (le_of_lt hs))
      · exact h.le
      · exact absurd h (not_lt.2 hθ.1.le)
      · exact absurd h (not_lt.2 hθ.2.le)
    simp [hK, abs_of_pos (show (0:ℝ) < s from hs), hF0 s hsR]
  have e1 : ∀ θ : ℝ, (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I =
      Complex.exp ((θ : ℂ) * Complex.I) := by
    intro θ; rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [polarCoord_target, setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    (g := K) (fun p _ => by
      simp only [hK, e1, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
        Real.norm_eq_abs, mul_one])]
  rw [Measure.volume_eq_prod, setIntegral_prod K (by rw [← Measure.volume_eq_prod]; exact hKint)]
  have hper : ∀ s : ℝ, ∫ θ in Ioo (-Real.pi) Real.pi, K (s, θ) =
      s * F |s| * ∫ θ in (0 : ℝ)..2 * Real.pi,
        g (c + (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    intro s
    simp only [hK, e1]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    have hP : Function.Periodic (fun θ : ℝ => s * (g (c + (s : ℂ) *
        Complex.exp ((θ : ℂ) * Complex.I)) * F |s|)) (2 * Real.pi) := by
      intro θ
      simp only
      congr 3
      rw [show ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I = (θ : ℂ) * Complex.I +
        2 * Real.pi * Complex.I by push_cast; ring]
      rw [Complex.exp_periodic]
    have := hP.intervalIntegral_add_eq (-Real.pi) 0
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at this
    rw [this, ← intervalIntegral.integral_const_mul]
    congr 1; funext θ; ring
  simp only [hper]
  rw [intervalIntegral.integral_of_le hR.le]
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
  · refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro s hs
    simp only [abs_of_pos hs.1]
    ring
  · rintro s ⟨hs, hn⟩
    simp only [mem_Ioc, not_and_or, not_le, mem_Ioi] at hn hs
    rcases hn with h | h
    · exact absurd hs (not_lt.2 (by simpa using h))
    · simp [abs_of_pos hs, hF0 s h.le]


theorem step_integrals (Ψ : ℝ → ℝ) (hd : ∀ x, HasDerivAt Ψ (deriv Ψ x) x)
    (hdd : ∀ x, HasDerivAt (deriv Ψ) (deriv (deriv Ψ) x) x)
    (hc1 : Continuous (deriv Ψ)) (hc2 : Continuous (deriv (deriv Ψ)))
    (h0 : Ψ 0 = 1) (h1 : Ψ 1 = 0) (h0' : deriv Ψ 0 = 0) (h1' : deriv Ψ 1 = 0) :
    (∫ τ in (0 : ℝ)..1, deriv (deriv Ψ) τ) = 0 ∧ (∫ τ in (0 : ℝ)..1, deriv Ψ τ) = -1 ∧
      (∫ τ in (0 : ℝ)..1, τ * deriv (deriv Ψ) τ) = 1 := by
  have e1 : (∫ τ in (0 : ℝ)..1, deriv (deriv Ψ) τ) = 0 := by
    rw [integral_eq_sub_of_hasDerivAt (fun x _ => hdd x) (hc2.intervalIntegrable 0 1), h0', h1',
      sub_zero]
  have e2 : (∫ τ in (0 : ℝ)..1, deriv Ψ τ) = -1 := by
    rw [integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc1.intervalIntegrable 0 1), h0, h1]
    norm_num
  have e3 : (∫ τ in (0 : ℝ)..1, (deriv Ψ τ + τ * deriv (deriv Ψ) τ)) = 0 := by
    have hD : ∀ x, HasDerivAt (fun τ => τ * deriv Ψ τ) (deriv Ψ x + x * deriv (deriv Ψ) x) x := by
      intro x
      have := (hasDerivAt_id x).mul (hdd x)
      simpa using this
    rw [integral_eq_sub_of_hasDerivAt (fun x _ => hD x)
      ((hc1.add (continuous_id.mul hc2)).intervalIntegrable 0 1), h0', h1']
    ring
  refine ⟨e1, e2, ?_⟩
  have i1 : IntervalIntegrable (fun τ => deriv Ψ τ) volume 0 1 := hc1.intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun τ => τ * deriv (deriv Ψ) τ) volume 0 1 :=
    (continuous_id.mul hc2).intervalIntegrable 0 1
  rw [integral_add i1 i2, e2] at e3
  linarith

/-- The one-dimensional radial limit (needs only differentiability of `I` at `r`). -/
theorem radial_limit (Ψ : ℝ → ℝ) (hd : ∀ x, HasDerivAt Ψ (deriv Ψ x) x)
    (hdd : ∀ x, HasDerivAt (deriv Ψ) (deriv (deriv Ψ) x) x)
    (hc1 : Continuous (deriv Ψ)) (hc2 : Continuous (deriv (deriv Ψ)))
    (h0 : Ψ 0 = 1) (h1 : Ψ 1 = 0) (h0' : deriv Ψ 0 = 0) (h1' : deriv Ψ 1 = 0)
    (I : ℝ → ℝ) {r h₀ : ℝ} (hr : 0 < r) (hh₀ : 0 < h₀) (hIc : ContinuousOn I (Icc r (r + h₀)))
    (hI : DifferentiableAt ℝ I r) :
    Tendsto (fun h : ℝ => ∫ τ in (0 : ℝ)..1,
        (deriv (deriv Ψ) τ / h + deriv Ψ τ / (r + h * τ)) * I (r + h * τ))
      (𝓝[>] 0) (𝓝 (deriv I r - I r / r)) := by
  obtain ⟨e1, e2, e3⟩ := step_integrals Ψ hd hdd hc1 hc2 h0 h1 h0' h1'
  set D := deriv I r with hD
  obtain ⟨K₂, hK₂⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc2.continuousOn
  obtain ⟨K₁, hK₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc1.continuousOn
  have hlo := hasDerivAt_iff_isLittleO.1 hI.hasDerivAt
  have hcq : ContinuousAt (fun x => I x / x) r := hI.continuousAt.div continuousAt_id hr.ne'
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ := ε / (4 * (|K₁| + |K₂| + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨ρ₁, hρ₁, hP1⟩ := Metric.eventually_nhds_iff.1 (hlo.def hδ0)
  obtain ⟨ρ₂, hρ₂, hP2⟩ := Metric.continuousAt_iff.1 hcq δ hδ0
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ h < min (min ρ₁ ρ₂) (min h₀ r) := by
    have : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < min (min ρ₁ ρ₂) (min h₀ r) :=
      nhdsWithin_le_nhds (gt_mem_nhds (by positivity))
    filter_upwards [self_mem_nhdsWithin, this] with h hpos hlt
    exact ⟨hpos, hlt⟩
  filter_upwards [hev] with h ⟨hpos, hlt⟩
  have hρ1 : h < ρ₁ := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_left _ _))
  have hρ2 : h < ρ₂ := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_right _ _))
  have hh0 : h ≤ h₀ := (lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_left _ _))).le
  -- continuity of the rescaled data on [0,1]
  have hIτ : ContinuousOn (fun τ => I (r + h * τ)) (Icc (0 : ℝ) 1) := by
    refine hIc.comp (continuous_const.add (continuous_const.mul continuous_id)).continuousOn ?_
    intro τ hτ
    constructor
    · nlinarith [hτ.1]
    · nlinarith [hτ.2]
  have hden : ∀ τ ∈ Icc (0 : ℝ) 1, 0 < r + h * τ := fun τ hτ => by nlinarith [hτ.1]
  have hinvc : ContinuousOn (fun τ => 1 / (r + h * τ)) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
      (fun τ hτ => (hden τ hτ).ne')
  have huIcc : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  -- the target as one integral
  set G : ℝ → ℝ := fun τ => deriv (deriv Ψ) τ * ((I (r + h * τ) - I r - h * τ * D) / h) +
    deriv Ψ τ * (I (r + h * τ) / (r + h * τ) - I r / r) with hG
  have hGc : ContinuousOn G (Icc (0 : ℝ) 1) := by
    refine (hc2.continuousOn.mul (((hIτ.sub continuousOn_const).sub
      ((continuousOn_const.mul continuousOn_id).mul continuousOn_const)).div_const h)).add
      (hc1.continuousOn.mul ((hIτ.mul hinvc |>.congr ?_).sub continuousOn_const))
    intro τ _; simp [div_eq_mul_inv]
  have hFc : ContinuousOn (fun τ => (deriv (deriv Ψ) τ / h + deriv Ψ τ / (r + h * τ)) *
      I (r + h * τ)) (Icc (0 : ℝ) 1) := by
    refine ((hc2.continuousOn.div_const h).add (hc1.continuousOn.mul hinvc |>.congr ?_)).mul hIτ
    intro τ _; simp [div_eq_mul_inv]
  have hsplit : (∫ τ in (0 : ℝ)..1, (deriv (deriv Ψ) τ / h + deriv Ψ τ / (r + h * τ)) *
      I (r + h * τ)) - (D - I r / r) = ∫ τ in (0 : ℝ)..1, G τ := by
    have iA : IntervalIntegrable (fun τ => D * (τ * deriv (deriv Ψ) τ)) volume 0 1 :=
      ((continuous_id.mul hc2).const_mul D).intervalIntegrable 0 1
    have iB : IntervalIntegrable (fun τ => I r / h * deriv (deriv Ψ) τ) volume 0 1 :=
      (hc2.const_mul _).intervalIntegrable 0 1
    have iC : IntervalIntegrable (fun τ => I r / r * deriv Ψ τ) volume 0 1 :=
      (hc1.const_mul _).intervalIntegrable 0 1
    have iAB : IntervalIntegrable (fun τ => D * (τ * deriv (deriv Ψ) τ) +
        I r / h * deriv (deriv Ψ) τ) volume 0 1 := iA.add iB
    have iL : IntervalIntegrable (fun τ => D * (τ * deriv (deriv Ψ) τ) +
        I r / h * deriv (deriv Ψ) τ + I r / r * deriv Ψ τ) volume 0 1 := iAB.add iC
    have iF : IntervalIntegrable (fun τ => (deriv (deriv Ψ) τ / h + deriv Ψ τ / (r + h * τ)) *
        I (r + h * τ)) volume 0 1 := ContinuousOn.intervalIntegrable (by rw [huIcc]; exact hFc)
    have hL : D - I r / r = ∫ τ in (0 : ℝ)..1, (D * (τ * deriv (deriv Ψ) τ) +
        I r / h * deriv (deriv Ψ) τ + I r / r * deriv Ψ τ) := by
      rw [integral_add iAB iC, integral_add iA iB,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, e1, e2, e3]
      ring
    rw [hL, ← integral_sub iF iL]
    refine integral_congr fun τ hτ => ?_
    rw [huIcc] at hτ
    have hne : r + h * τ ≠ 0 := (hden τ hτ).ne'
    simp only [hG]
    field_simp
    ring
  -- pointwise bound on G
  have hGb : ∀ τ ∈ Set.uIoc (0 : ℝ) 1, ‖G τ‖ ≤ |K₂| * δ + |K₁| * δ := by
    intro τ hτ
    have hτ' : τ ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at hτ; exact ⟨hτ.1.le, hτ.2⟩
    have hx : dist (r + h * τ) r < ρ₁ := by
      rw [Real.dist_eq, show r + h * τ - r = h * τ by ring, abs_of_nonneg (by nlinarith [hτ'.1])]
      nlinarith [hτ'.2]
    have hx2 : dist (r + h * τ) r < ρ₂ := by
      rw [Real.dist_eq, show r + h * τ - r = h * τ by ring, abs_of_nonneg (by nlinarith [hτ'.1])]
      nlinarith [hτ'.2]
    have b1 := hP1 hx
    simp only [Real.norm_eq_abs, smul_eq_mul, show r + h * τ - r = h * τ by ring] at b1
    have b1' : |(I (r + h * τ) - I r - h * τ * D) / h| ≤ δ := by
      rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      have : |h * τ| ≤ h := by
        rw [abs_of_nonneg (by nlinarith [hτ'.1])]; nlinarith [hτ'.2]
      have e : h * τ * D = h * τ * D := rfl
      calc |I (r + h * τ) - I r - h * τ * D| ≤ δ * |h * τ| := by
            simpa [mul_comm] using b1
        _ ≤ δ * h := mul_le_mul_of_nonneg_left this hδ0.le
    have b2 := hP2 hx2
    rw [Real.dist_eq] at b2
    have k2 : |deriv (deriv Ψ) τ| ≤ |K₂| := (by simpa using hK₂ τ hτ' : |deriv (deriv Ψ) τ| ≤ K₂).trans
      (le_abs_self _)
    have k1 : |deriv Ψ τ| ≤ |K₁| := (by simpa using hK₁ τ hτ' : |deriv Ψ τ| ≤ K₁).trans
      (le_abs_self _)
    simp only [hG, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul k2 b1' (abs_nonneg _) (abs_nonneg _))
      (mul_le_mul k1 b2.le (abs_nonneg _) (abs_nonneg _))
  have hnorm := norm_integral_le_of_norm_le_const hGb
  rw [Real.dist_eq, hsplit]
  calc |∫ τ in (0 : ℝ)..1, G τ| ≤ (|K₂| * δ + |K₁| * δ) * |(1 : ℝ) - 0| := hnorm
    _ < ε := by
      rw [sub_zero, abs_one, mul_one, hδ]
      rw [← add_mul, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg K₁, abs_nonneg K₂]

theorem cont_zero_left {φ : ℝ → ℝ} (hφ : Continuous φ) {a : ℝ} (h : ∀ x, x < a → φ x = 0) :
    φ a = 0 := by
  have h1 : Tendsto φ (𝓝[<] a) (𝓝 (φ a)) := hφ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto φ (𝓝[<] a) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (h y hy).symm
  exact tendsto_nhds_unique h1 h2

theorem cont_zero_right {φ : ℝ → ℝ} (hφ : Continuous φ) {a : ℝ} (h : ∀ x, a < x → φ x = 0) :
    φ a = 0 := by
  have h1 : Tendsto φ (𝓝[>] a) (𝓝 (φ a)) := hφ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto φ (𝓝[>] a) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (h y hy).symm
  exact tendsto_nhds_unique h1 h2

/-- A function locally constant near `x` has vanishing first and second derivatives there. -/
theorem derivs_zero_of_eventuallyEq_const {φ : ℝ → ℝ} {x a : ℝ} (h : ∀ᶠ y in 𝓝 x, φ y = a) :
    deriv φ x = 0 ∧ deriv (deriv φ) x = 0 := by
  have h1 : ∀ᶠ y in 𝓝 x, deriv φ y = 0 := by
    filter_upwards [h.eventually_nhds] with y hy
    have : φ =ᶠ[𝓝 y] fun _ => a := hy
    rw [this.deriv_eq, deriv_const]
  refine ⟨h1.self_of_nhds, ?_⟩
  have : deriv φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := h1
  rw [this.deriv_eq, deriv_const]

theorem cdPsi_derivs_vanish :
    (∀ x : ℝ, x ≤ 0 → deriv cdPsi x = 0 ∧ deriv (deriv cdPsi) x = 0) ∧
    (∀ x : ℝ, 1 ≤ x → deriv cdPsi x = 0 ∧ deriv (deriv cdPsi) x = 0) := by
  have hl : ∀ x : ℝ, x < 0 → deriv cdPsi x = 0 ∧ deriv (deriv cdPsi) x = 0 := fun x hx =>
    derivs_zero_of_eventuallyEq_const (a := 1) (by
      filter_upwards [Iio_mem_nhds hx] with y hy using cdPsi_of_nonpos (le_of_lt hy))
  have hr : ∀ x : ℝ, 1 < x → deriv cdPsi x = 0 ∧ deriv (deriv cdPsi) x = 0 := fun x hx =>
    derivs_zero_of_eventuallyEq_const (a := 0) (by
      filter_upwards [Ioi_mem_nhds hx] with y hy using cdPsi_of_one_le (le_of_lt hy))
  have c1 := cdPsi_deriv_contDiff.continuous
  have c2 := cdPsi_deriv2_contDiff.continuous
  constructor
  · intro x hx
    rcases hx.lt_or_eq with hx | rfl
    · exact hl x hx
    · exact ⟨cont_zero_left c1 (fun y hy => (hl y hy).1), cont_zero_left c2 (fun y hy => (hl y hy).2)⟩
  · intro x hx
    rcases hx.lt_or_eq with hx | rfl
    · exact hr x hx
    · exact ⟨cont_zero_right c1 (fun y hy => (hr y hy).1),
        cont_zero_right c2 (fun y hy => (hr y hy).2)⟩

/-- C1-4: the Laplacian pairing with radial cutoffs tends to `I'(r) - I(r)/r`. -/
theorem C14_limit (c : ℂ) (g : ℂ → ℝ) (hg : Continuous g) {r : ℝ} (hr : 0 < r)
    (hI : DifferentiableAt ℝ (fun s : ℝ => s * ∫ θ in (0 : ℝ)..2 * Real.pi,
      g (c + (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) r) :
    Tendsto (fun h : ℝ => ∫ z, g z *
        Laplacian.laplacian (fun w => cdPsi ((Real.sqrt (‖w - c‖ ^ 2) - r) / h)) z)
      (𝓝[>] 0) (𝓝 (deriv (fun s : ℝ => s * ∫ θ in (0 : ℝ)..2 * Real.pi,
        g (c + (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) r -
        (r * ∫ θ in (0 : ℝ)..2 * Real.pi,
          g (c + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) / r)) := by
  set I : ℝ → ℝ := fun s : ℝ => s * ∫ θ in (0 : ℝ)..2 * Real.pi,
      g (c + (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) with hIdef
  have hIc : Continuous I := by
    refine continuous_id.mul ?_
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
    exact hg.comp (by fun_prop)
  obtain ⟨hd, hdd, hc1, hc2, h0, h1, h0', h1'⟩ := cdPsi_facts
  obtain ⟨hv0, hv1⟩ := cdPsi_derivs_vanish
  have key : ∀ h : ℝ, 0 < h → (∫ z, g z *
      Laplacian.laplacian (fun w => cdPsi ((Real.sqrt (‖w - c‖ ^ 2) - r) / h)) z) =
      ∫ τ in (0 : ℝ)..1, (deriv (deriv cdPsi) τ / h + deriv cdPsi τ / (r + h * τ)) *
        I (r + h * τ) := by
    intro h hh
    set Φ : ℝ → ℝ := fun t => cdPsi ((Real.sqrt t - r) / h) with hΦ
    have hΦ' : ContDiff ℝ ∞ (deriv Φ) :=
      (contDiff_infty_iff_deriv.1 (radPhi_contDiff hr hh ⊤)).2
    have hΦ'' : ContDiff ℝ ∞ (deriv (deriv Φ)) := (contDiff_infty_iff_deriv.1 hΦ').2
    have hdΦ : Differentiable ℝ Φ := (radPhi_contDiff hr hh 1).differentiable (by norm_num)
    have hddΦ : Differentiable ℝ (deriv Φ) := hΦ'.differentiable (by simp)
    set F : ℝ → ℝ := fun s => 4 * deriv Φ (s ^ 2) + 4 * s ^ 2 * deriv (deriv Φ) (s ^ 2) with hF
    have hFc : Continuous F := by
      simp only [hF]
      exact (continuous_const.mul (hΦ'.continuous.comp (continuous_pow 2))).add
        ((continuous_const.mul (continuous_pow 2)).mul (hΦ''.continuous.comp (continuous_pow 2)))
    -- F in terms of the profile
    have hprof : ∀ s : ℝ, 0 < s → F s = deriv (deriv cdPsi) ((s - r) / h) / h ^ 2 +
        deriv cdPsi ((s - r) / h) / (h * s) := fun s hs => radPhi_profile hh hs
    have hlow : ∀ s : ℝ, s ^ 2 < r ^ 2 → F s = 0 := by
      intro s hs
      have hloc : ∀ᶠ t in 𝓝 (s ^ 2), Φ t = 1 := by
        filter_upwards [Iio_mem_nhds hs] with y hy
        apply cdPsi_of_nonpos
        have : Real.sqrt y < r := (Real.sqrt_lt' hr).2 hy
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) hh.le
      obtain ⟨e1, e2⟩ := derivs_zero_of_eventuallyEq_const hloc
      simp only [hF, e1, e2]; ring
    have hzero : ∀ s : ℝ, 0 ≤ s → (s ≤ r ∨ r + h ≤ s) → F s = 0 := by
      intro s hs0 hs
      rcases hs with hs | hs
      · rcases hs.lt_or_eq with hs | rfl
        · exact hlow s (by nlinarith)
        · rw [hprof _ hr, sub_self, zero_div, (hv0 0 le_rfl).1, (hv0 0 le_rfl).2]; ring
      · have hpos : 0 < s := by linarith
        have h1le : 1 ≤ (s - r) / h := by rw [le_div_iff₀ hh]; linarith
        rw [hprof s hpos, (hv1 _ h1le).1, (hv1 _ h1le).2]; ring
    have hlap : ∀ z : ℂ, Laplacian.laplacian
        (fun w => cdPsi ((Real.sqrt (‖w - c‖ ^ 2) - r) / h)) z = F ‖z - c‖ := by
      intro z
      have := lap_radial Φ hdΦ hddΦ c z
      simp only [hF]
      exact this
    simp only [hlap]
    rw [polar_radial c (R := r + 2 * h) (by positivity) g hg F hFc
      (fun s hs => hzero s (by linarith) (Or.inr (by linarith)))]
    have hint : ∀ a b : ℝ, IntervalIntegrable (fun s => F s * I s) volume a b :=
      fun a b => (hFc.mul hIc).intervalIntegrable a b
    change ∫ s in (0 : ℝ)..r + 2 * h, F s * I s = _
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 r) (hint r (r + 2 * h)),
      ← intervalIntegral.integral_add_adjacent_intervals (hint r (r + h)) (hint (r + h) (r + 2 * h))]
    have z1 : ∫ s in (0 : ℝ)..r, F s * I s = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs => by
        rw [uIcc_of_le hr.le] at hs
        simp only [hzero s hs.1 (Or.inl hs.2), zero_mul])]
      simp
    have z2 : ∫ s in r + h..r + 2 * h, F s * I s = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs => by
        rw [uIcc_of_le (by linarith)] at hs
        simp only [hzero s (by linarith [hs.1]) (Or.inr hs.1), zero_mul])]
      simp
    rw [z1, z2, zero_add, add_zero]
    have hsub := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
      (fun s => F s * I s) hh.ne' r
    simp only [mul_zero, zero_add, mul_one] at hsub
    have hmain : ∫ s in r..h + r, F s * I s = h * ∫ τ in (0 : ℝ)..1, F (h * τ + r) * I (h * τ + r) := by
      rw [hsub, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
    rw [add_comm r h, hmain, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun τ hτ => ?_)
    rw [uIcc_of_le zero_le_one] at hτ
    have hs : 0 < h * τ + r := by nlinarith [hτ.1]
    rw [hprof _ hs, show (h * τ + r - r) / h = τ by field_simp; ring, add_comm (h * τ) r]
    field_simp
  have hlim := radial_limit cdPsi hd hdd hc1 hc2 h0 h1 h0' h1' I hr (h₀ := 1) one_pos
    hIc.continuousOn hI
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (key h hh).symm


/-! ## L3: mean value inequality for continuous, nonnegative, weakly subharmonic functions.
Plateau `σ` in `t = ‖z - x‖²` with independent edge widths, `q = σ / t`, `Φ t = -∫ B..t q`,
test function `η = Φ (‖z - x‖²)`, `Δη = -4 σ'(‖z - x‖²)`. -/

theorem cdPsi_deriv_nonpos (x : ℝ) : deriv cdPsi x ≤ 0 := by
  have h : deriv cdPsi x = -deriv Real.smoothTransition x := by
    unfold cdPsi
    rw [deriv_const_sub]
  rw [h, neg_nonpos]
  exact Real.smoothTransition.monotone.deriv_nonneg

theorem cdPsi_deriv_bound : ∃ M : ℝ, 0 < M ∧ ∀ x, |deriv cdPsi x| ≤ M := by
  obtain ⟨-, -, hc1, -⟩ := cdPsi_facts
  obtain ⟨hv0, hv1⟩ := cdPsi_derivs_vanish
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc1.continuousOn
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x => ?_⟩
  rcases le_or_gt x 0 with h | h
  · rw [(hv0 x h).1, abs_zero]; exact le_trans zero_le_one (le_max_right _ _)
  rcases le_or_gt 1 x with h' | h'
  · rw [(hv1 x h').1, abs_zero]; exact le_trans zero_le_one (le_max_right _ _)
  · have := hM x ⟨h.le, h'.le⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

/-- The plateau `σ`: `0` for `t ≤ α`, `1` on `[α + k, β]`, `0` for `t ≥ β + l`. -/
noncomputable def plat (α k β l t : ℝ) : ℝ := (1 - cdPsi ((t - α) / k)) * cdPsi ((t - β) / l)

theorem plat_contDiff (α k β l : ℝ) : ContDiff ℝ ∞ (plat α k β l) := by
  unfold plat
  have h := cdPsi_contDiff ⊤
  exact (contDiff_const.sub (h.comp ((contDiff_id.sub contDiff_const).div_const k))).mul
    (h.comp ((contDiff_id.sub contDiff_const).div_const l))

theorem plat_low {α k β l t : ℝ} (hk : 0 < k) (ht : t ≤ α) : plat α k β l t = 0 := by
  unfold plat
  rw [cdPsi_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hk.le)]; ring

theorem plat_high {α k β l t : ℝ} (hl : 0 < l) (ht : β + l ≤ t) : plat α k β l t = 0 := by
  unfold plat
  rw [cdPsi_of_one_le (x := (t - β) / l) (by rw [le_div_iff₀ hl]; linarith)]; ring

theorem plat_nonneg (α k β l t : ℝ) : 0 ≤ plat α k β l t := by
  unfold plat
  have h1 := cdPsi_mem ((t - α) / k)
  have h2 := cdPsi_mem ((t - β) / l)
  exact mul_nonneg (by linarith [h1.2]) h2.1

theorem plat_deriv {α k β l : ℝ} (hk : 0 < k) (hl : 0 < l) (hab : α + k ≤ β) (t : ℝ) :
    deriv (plat α k β l) t = -(deriv cdPsi ((t - α) / k) / k) + deriv cdPsi ((t - β) / l) / l := by
  obtain ⟨hd, -⟩ := cdPsi_facts
  obtain ⟨hv0, hv1⟩ := cdPsi_derivs_vanish
  have hA := (hd ((t - α) / k)).comp t (((hasDerivAt_id t).sub_const α).div_const k)
  have hB := (hd ((t - β) / l)).comp t (((hasDerivAt_id t).sub_const β).div_const l)
  have hP := ((hasDerivAt_const t (1 : ℝ)).sub hA).mul hB
  have e : plat α k β l = ((fun _ => (1 : ℝ)) - cdPsi ∘ fun x => (id x - α) / k) *
      (cdPsi ∘ fun x => (id x - β) / l) := by
    funext y; simp [plat]
  rw [e, hP.deriv]
  simp only [Pi.sub_apply, Function.comp_apply, id]
  rcases le_or_gt t β with htb | htb
  · have h0 : (t - β) / l ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hl.le
    rw [cdPsi_of_nonpos (x := (t - β) / l) h0, (hv0 ((t - β) / l) h0).1]
    ring
  · have h1 : 1 ≤ (t - α) / k := by rw [le_div_iff₀ hk]; linarith
    rw [cdPsi_of_one_le h1, (hv1 _ h1).1]
    ring

/-- `q = σ / t` is smooth (it vanishes near `t ≤ α`, `α > 0`). -/
theorem platq_contDiff {α k β l : ℝ} (hα : 0 < α) (hk : 0 < k) :
    ContDiff ℝ ∞ (fun t => plat α k β l t / t) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge t α with ht | ht
  · have : (fun t => plat α k β l t / t) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with y hy
      rw [plat_low hk hy.le, zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · exact ((plat_contDiff α k β l).contDiffAt).div contDiffAt_id (by linarith)

/-- The potential `Φ t = -∫ B..t q` with `B = β + l`. -/
noncomputable def platPhi (α k β l t : ℝ) : ℝ := -∫ τ in (β + l)..t, plat α k β l τ / τ

theorem platPhi_hasDerivAt {α k β l : ℝ} (hα : 0 < α) (hk : 0 < k) (t : ℝ) :
    HasDerivAt (platPhi α k β l) (-(plat α k β l t / t)) t := by
  have hq := (platq_contDiff (β := β) (l := l) hα hk).continuous
  exact ((hq.integral_hasStrictDerivAt (β + l) t).hasDerivAt).neg

theorem platPhi_deriv {α k β l : ℝ} (hα : 0 < α) (hk : 0 < k) :
    deriv (platPhi α k β l) = fun t => -(plat α k β l t / t) := by
  funext t; exact (platPhi_hasDerivAt hα hk t).deriv

theorem platPhi_contDiff {α k β l : ℝ} (hα : 0 < α) (hk : 0 < k) :
    ContDiff ℝ ∞ (platPhi α k β l) := by
  refine contDiff_infty_iff_deriv.2 ⟨fun t => (platPhi_hasDerivAt hα hk t).differentiableAt, ?_⟩
  rw [platPhi_deriv hα hk]
  exact (platq_contDiff hα hk).neg

theorem platPhi_nonneg {α k β l : ℝ} (hα : 0 < α) (hk : 0 < k) (hl : 0 < l) (t : ℝ) :
    0 ≤ platPhi α k β l t := by
  unfold platPhi
  rcases le_or_gt t (β + l) with ht | ht
  · rw [intervalIntegral.integral_symm, neg_neg]
    refine intervalIntegral.integral_nonneg ht (fun τ hτ => ?_)
    rcases le_or_gt τ 0 with h0 | h0
    · rw [plat_low hk (by linarith)]; simp
    · exact div_nonneg (plat_nonneg _ _ _ _ _) h0.le
  · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun τ hτ => by
      rw [uIcc_of_le ht.le] at hτ
      simp only [plat_high hl hτ.1, zero_div])]
    simp

theorem platPhi_high {α k β l : ℝ} (hl : 0 < l) {t : ℝ} (ht : β + l ≤ t) :
    platPhi α k β l t = 0 := by
  unfold platPhi
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun τ hτ => by
    rw [uIcc_of_le ht] at hτ
    simp only [plat_high hl hτ.1, zero_div])]
  simp

/-- Radial profile of `Δ (platPhi (‖· - x‖²))`: `4Φ'(t) + 4tΦ''(t) = -4σ'(t)`. -/
theorem platPhi_profile {α k β l : ℝ} (hα : 0 < α) (hk : 0 < k) (t : ℝ) :
    4 * deriv (platPhi α k β l) t + 4 * t * deriv (deriv (platPhi α k β l)) t =
      -4 * deriv (plat α k β l) t := by
  have hq := platq_contDiff (β := β) (l := l) hα hk
  have hqd : DifferentiableAt ℝ (fun t => plat α k β l t / t) t :=
    hq.differentiable (by simp) t
  have htq : (id * fun t => plat α k β l t / t) = plat α k β l := by
    funext y
    simp only [Pi.mul_apply, id]
    rcases eq_or_ne y 0 with rfl | hy
    · rw [plat_low hk hα.le]; simp
    · field_simp
  have hprod := (hasDerivAt_id t).mul hqd.hasDerivAt
  rw [htq] at hprod
  rw [platPhi_deriv hα hk,
    show (fun t => -(plat α k β l t / t)) = -(fun t => plat α k β l t / t) from rfl,
    deriv.neg', hprod.deriv]
  simp only [Pi.neg_apply, id]
  ring

theorem plat_lap (x : ℂ) {α k β l : ℝ} (hα : 0 < α) (hk : 0 < k) (z : ℂ) :
    Laplacian.laplacian (fun w => platPhi α k β l (‖w - x‖ ^ 2)) z =
      -4 * deriv (plat α k β l) (‖z - x‖ ^ 2) := by
  have hΦ := platPhi_contDiff (β := β) (l := l) hα hk
  have hΦ' : ContDiff ℝ ∞ (deriv (platPhi α k β l)) := (contDiff_infty_iff_deriv.1 hΦ).2
  rw [lap_radial _ (hΦ.differentiable (by simp)) (hΦ'.differentiable (by simp)) x z,
    platPhi_profile hα hk]

/-- Mass of the radial bump kernel `-(Ψ'((‖z-x‖²-a)/k)/k)`: it equals `π`. -/
theorem bump_mass (x : ℂ) {a k R : ℝ} (ha : 0 ≤ a) (hk : 0 < k) (hR : 0 < R)
    (haR : a + k ≤ R ^ 2) :
    ∫ z, -(deriv cdPsi ((‖z - x‖ ^ 2 - a) / k) / k) = Real.pi := by
  obtain ⟨hd, -, hc1, -⟩ := cdPsi_facts
  have hin : Continuous (fun s : ℝ => (s ^ 2 - a) / k) :=
    ((continuous_pow 2).sub continuous_const).div_const k
  have hF : Continuous (fun s : ℝ => -(deriv cdPsi ((s ^ 2 - a) / k) / k)) :=
    ((hc1.comp hin).div_const k).neg
  have hpol := polar_radial x hR (fun _ => (1 : ℝ)) continuous_const _ hF (fun s hs => by
    have h1 : 1 ≤ (s ^ 2 - a) / k := by rw [le_div_iff₀ hk]; nlinarith
    rw [(cdPsi_derivs_vanish.2 _ h1).1]; simp)
  simp only [one_mul] at hpol
  rw [hpol]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  have hD : ∀ s ∈ uIcc (0 : ℝ) R, HasDerivAt (fun s => cdPsi ((s ^ 2 - a) / k))
      (deriv cdPsi ((s ^ 2 - a) / k) * (2 * s / k)) s := by
    intro s _
    have h2 : HasDerivAt (fun s : ℝ => (s ^ 2 - a) / k) (2 * s / k) s := by
      have := ((hasDerivAt_pow 2 s).sub_const a).div_const k
      convert this using 1; ring
    exact (hd _).comp s h2
  have hcont : Continuous (fun s : ℝ => deriv cdPsi ((s ^ 2 - a) / k) * (2 * s / k)) :=
    (hc1.comp hin).mul ((continuous_const.mul continuous_id).div_const k)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hD (hcont.intervalIntegrable 0 R)
  have e : (fun s : ℝ => -(deriv cdPsi ((s ^ 2 - a) / k) / k) * (s * (2 * Real.pi))) =
      fun s => (-Real.pi) * (deriv cdPsi ((s ^ 2 - a) / k) * (2 * s / k)) := by
    funext s; ring
  rw [e, intervalIntegral.integral_const_mul, hint]
  have h1 : 1 ≤ (R ^ 2 - a) / k := by rw [le_div_iff₀ hk]; linarith
  have h0 : ((0 : ℝ) ^ 2 - a) / k ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by simp; linarith) hk.le
  rw [cdPsi_of_one_le h1, cdPsi_of_nonpos h0]
  ring

/-- The radial bump kernel `-(Ψ'((‖z-x‖²-a)/k)/k)` (nonnegative, mass `π`, supported in
`‖z - x‖² ≤ a + k`). -/
noncomputable def bumpK (x : ℂ) (a k : ℝ) (z : ℂ) : ℝ :=
  -(deriv cdPsi ((‖z - x‖ ^ 2 - a) / k) / k)

theorem bumpK_continuous (x : ℂ) (a k : ℝ) : Continuous (bumpK x a k) := by
  obtain ⟨-, -, hc1, -⟩ := cdPsi_facts
  unfold bumpK
  exact ((hc1.comp ((((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2).sub
    continuous_const).div_const k)).div_const k).neg

theorem bumpK_zero (x : ℂ) {a k : ℝ} (hk : 0 < k) {z : ℂ} (hz : a + k ≤ ‖z - x‖ ^ 2) :
    bumpK x a k z = 0 := by
  unfold bumpK
  rw [(cdPsi_derivs_vanish.2 _ (by rw [le_div_iff₀ hk]; linarith)).1]; simp

theorem bumpK_nonneg (x : ℂ) {a k : ℝ} (hk : 0 < k) (z : ℂ) : 0 ≤ bumpK x a k z := by
  unfold bumpK
  exact neg_nonneg.2 (div_nonpos_of_nonpos_of_nonneg (cdPsi_deriv_nonpos _) hk.le)

theorem bumpK_le (x : ℂ) {a k M : ℝ} (hk : 0 < k) (hM : ∀ x, |deriv cdPsi x| ≤ M) (z : ℂ) :
    bumpK x a k z ≤ M / k := by
  unfold bumpK
  rw [← neg_div]
  exact (div_le_div_iff_of_pos_right hk).2 (le_trans (neg_le_abs _) (hM _))

theorem fK_integrable (x : ℂ) (f : ℂ → ℝ) (hf : Continuous f) {a k : ℝ} (hk : 0 < k)
    (_ha : 0 ≤ a) : Integrable (fun z => f z * bumpK x a k z) := by
  refine (hf.mul (bumpK_continuous x a k)).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall x (Real.sqrt (a + k))) (fun z hz => ?_)
  rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hz
  have h2 : a + k ≤ ‖z - x‖ ^ 2 :=
    ((Real.sqrt_lt' (lt_of_le_of_lt (Real.sqrt_nonneg _) hz)).1 hz).le
  show f z * bumpK x a k z = 0
  rw [bumpK_zero x hk h2, mul_zero]

theorem bump_mass' (x : ℂ) {a k : ℝ} (ha : 0 ≤ a) (hk : 0 < k) :
    ∫ z, bumpK x a k z = Real.pi := by
  unfold bumpK
  exact bump_mass x ha hk (R := a + k + 1) (by linarith) (by nlinarith)

theorem plat_lap_bumps (x : ℂ) {δ β : ℝ} (hδ : 0 < δ) (hβ : 0 < β) (hδβ : δ + δ ≤ β) (z : ℂ) :
    Laplacian.laplacian (fun w => platPhi δ δ β β (‖w - x‖ ^ 2)) z =
      4 * bumpK x β β z - 4 * bumpK x δ δ z := by
  rw [plat_lap x hδ hδ z, plat_deriv hδ hβ hδβ]
  unfold bumpK
  ring

/-- **L3** (mean value inequality): a continuous nonnegative `f` that is weakly subharmonic on
`ball x ρ₀` satisfies `f x ≤ C ρ⁻² ∫_{B(x,ρ)} f` for `ρ < ρ₀`, with a universal constant `C`. -/
theorem L3_mvi : ∃ C : ℝ, 0 < C ∧ ∀ (x : ℂ) (f : ℂ → ℝ), Continuous f → (∀ z, 0 ≤ f z) →
    ∀ ρ₀ : ℝ, (∀ η : ℂ → ℝ, ContDiff ℝ 2 η → (∀ z, 0 ≤ η z) →
      (∃ ρ₁ < ρ₀, ∀ z, ρ₁ ≤ dist z x → η z = 0) →
      0 ≤ ∫ z, f z * Laplacian.laplacian η z) →
    ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → f x ≤ C / ρ ^ 2 * ∫ z in Metric.ball x ρ, f z := by
  obtain ⟨M, hM0, hM⟩ := cdPsi_deriv_bound
  refine ⟨2 * M / Real.pi, by positivity, ?_⟩
  intro x f hf hf0 ρ₀ hsub ρ hρ hρρ
  set β : ℝ := ρ ^ 2 / 2 with hβ
  have hβ0 : 0 < β := by positivity
  have key : ∀ δ : ℝ, 0 < δ → δ + δ ≤ β →
      ∫ z, f z * bumpK x δ δ z ≤ ∫ z, f z * bumpK x β β z := by
    intro δ hδ hδβ
    have hc2 : ContDiff ℝ 2 (fun w : ℂ => platPhi δ δ β β (‖w - x‖ ^ 2)) :=
      contDiff_infty.1 ((platPhi_contDiff hδ hδ).comp ((contDiff_norm_sq ℝ).comp
        (contDiff_id.sub contDiff_const))) 2
    have hη := hsub (fun w => platPhi δ δ β β (‖w - x‖ ^ 2)) hc2
      (fun z => platPhi_nonneg hδ hδ hβ0 _)
      ⟨ρ, hρρ, fun z hz => platPhi_high hβ0 (by
        rw [dist_eq_norm] at hz
        have : ρ ^ 2 ≤ ‖z - x‖ ^ 2 := pow_le_pow_left₀ hρ.le hz 2
        linarith)⟩
    simp only [plat_lap_bumps x hδ hβ0 hδβ] at hη
    have e : (fun z => f z * (4 * bumpK x β β z - 4 * bumpK x δ δ z)) =
        fun z => 4 * (f z * bumpK x β β z) - 4 * (f z * bumpK x δ δ z) := by
      funext z; ring
    rw [e, integral_sub ((fK_integrable x f hf hβ0 hβ0.le).const_mul 4)
      ((fK_integrable x f hf hδ hδ.le).const_mul 4), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul] at hη
    linarith
  -- outer bound
  have hball : IntegrableOn f (Metric.ball x ρ) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall x ρ)).mono_set
      Metric.ball_subset_closedBall
  have hout : ∫ z, f z * bumpK x β β z ≤ (M / β) * ∫ z in Metric.ball x ρ, f z := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.ball x ρ) (fun z hz => by
      rw [Metric.mem_ball, dist_eq_norm, not_lt] at hz
      have : ρ ^ 2 ≤ ‖z - x‖ ^ 2 := pow_le_pow_left₀ hρ.le hz 2
      rw [bumpK_zero x hβ0 (by linarith), mul_zero])]
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_mono_on (fK_integrable x f hf hβ0 hβ0.le).integrableOn
      (hball.const_mul _) Metric.isOpen_ball.measurableSet (fun z _ => ?_)
    rw [mul_comm (M / β)]
    exact mul_le_mul_of_nonneg_left (bumpK_le x hβ0 hM z) (hf0 z)
  -- inner lower bound
  have hinner : ∀ ε > 0, (f x - ε) * Real.pi ≤ (M / β) * ∫ z in Metric.ball x ρ, f z := by
    intro ε hε
    obtain ⟨δ₀, hδ₀, hcont⟩ := Metric.continuous_iff.1 hf x ε hε
    set δ : ℝ := min (β / 2) (δ₀ ^ 2 / 4) with hδdef
    have hδ : 0 < δ := lt_min (by positivity) (by positivity)
    have hδβ : δ + δ ≤ β := by have := min_le_left (β / 2) (δ₀ ^ 2 / 4); linarith
    have hδ0 : δ + δ < δ₀ ^ 2 := by
      have := min_le_right (β / 2) (δ₀ ^ 2 / 4); nlinarith
    have hlow : ∫ z, (f x - ε) * bumpK x δ δ z ≤ ∫ z, f z * bumpK x δ δ z := by
      refine integral_mono ((bumpK_continuous x δ δ).integrable_of_hasCompactSupport ?_ |>.const_mul _)
        (fK_integrable x f hf hδ hδ.le) (fun z => ?_)
      · refine HasCompactSupport.intro (isCompact_closedBall x (Real.sqrt (δ + δ)))
          (fun z hz => ?_)
        rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hz
        exact bumpK_zero x hδ
          ((Real.sqrt_lt' (lt_of_le_of_lt (Real.sqrt_nonneg _) hz)).1 hz).le
      · by_cases hz : δ + δ ≤ ‖z - x‖ ^ 2
        · simp only [bumpK_zero x hδ hz, mul_zero, le_refl]
        · replace hz := not_le.1 hz
          have hd : dist z x < δ₀ := by
            rw [dist_eq_norm]
            by_contra hc
            replace hc := not_lt.1 hc
            nlinarith [norm_nonneg (z - x)]
          have := hcont z hd
          rw [Real.dist_eq, abs_lt] at this
          exact mul_le_mul_of_nonneg_right (by linarith) (bumpK_nonneg x hδ z)
    rw [MeasureTheory.integral_const_mul, bump_mass' x hδ.le hδ] at hlow
    linarith [key δ hδ hδβ]
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have h1 := hinner ε hε
  have hπ := Real.pi_pos
  have h2 : f x - ε ≤ (M / β) * (∫ z in Metric.ball x ρ, f z) / Real.pi :=
    (le_div_iff₀ hπ).2 h1
  have h3 : (M / β) * (∫ z in Metric.ball x ρ, f z) / Real.pi =
      2 * M / Real.pi / ρ ^ 2 * ∫ z in Metric.ball x ρ, f z := by
    rw [hβ]; field_simp
  linarith


theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℂ) (f : ℂ → ℝ), Continuous f → (∀ z, 0 ≤ f z) →
      ∀ ρ₀ : ℝ, (∀ η : ℂ → ℝ, ContDiff ℝ 2 η → (∀ z, 0 ≤ η z) →
        (∃ ρ₁ < ρ₀, ∀ z, ρ₁ ≤ dist z x → η z = 0) →
        0 ≤ ∫ z, f z * Laplacian.laplacian η z) →
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → f x ≤ C / ρ ^ 2 * ∫ z in Metric.ball x ρ, f z := by
  exact L3_mvi
