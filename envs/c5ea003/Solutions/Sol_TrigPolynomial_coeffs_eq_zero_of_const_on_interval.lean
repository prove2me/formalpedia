-- Prove2me | solution 1 for TrigPolynomial.coeffs_eq_zero_of_const_on_interval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T12:38:06.209735+00:00
-- url     : https://prove2.me/submissions/59d078f9-7a8b-4433-ad5b-bde2de972d9a

import Mathlib

theorem solution (A B alpha c theta0 delta : ℝ) (halpha : alpha ≠ 0)
    (hdelta : 0 < delta)
    (h : ∀ theta : ℝ, |theta - theta0| < delta →
      A * Real.cos (2 * alpha * theta) + B * Real.sin (2 * alpha * theta) = c) :
    A = 0 ∧ B = 0 ∧ c = 0 := by
  set f : ℝ → ℝ :=
    fun t => A * Real.cos (2 * alpha * t) + B * Real.sin (2 * alpha * t) with hfdef
  set fp : ℝ → ℝ :=
    fun t => A * (-Real.sin (2 * alpha * t) * (2 * alpha))
      + B * (Real.cos (2 * alpha * t) * (2 * alpha)) with hfpdef
  set fpp : ℝ → ℝ :=
    fun t => A * (-(Real.cos (2 * alpha * t) * (2 * alpha)) * (2 * alpha))
      + B * (-Real.sin (2 * alpha * t) * (2 * alpha) * (2 * alpha)) with hfppdef
  have hlin : ∀ t : ℝ, HasDerivAt (fun s : ℝ => 2 * alpha * s) (2 * alpha) t := by
    intro t
    simpa using (hasDerivAt_id t).const_mul (2 * alpha)
  have hf : ∀ t : ℝ, HasDerivAt f (fp t) t := by
    intro t
    exact (((Real.hasDerivAt_cos (2 * alpha * t)).comp t (hlin t)).const_mul A).add
      (((Real.hasDerivAt_sin (2 * alpha * t)).comp t (hlin t)).const_mul B)
  have hfp : ∀ t : ℝ, HasDerivAt fp (fpp t) t := by
    intro t
    exact ((((Real.hasDerivAt_sin (2 * alpha * t)).comp t (hlin t)).neg.mul_const
      (2 * alpha)).const_mul A).add
      ((((Real.hasDerivAt_cos (2 * alpha * t)).comp t (hlin t)).mul_const
        (2 * alpha)).const_mul B)
  -- `f` is constant on the interval, hence `fp` vanishes there
  have hIoo : ∀ t ∈ Set.Ioo (theta0 - delta) (theta0 + delta), f t = c := by
    intro t ht
    refine h t ?_
    rw [abs_sub_lt_iff]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hfp0 : ∀ t ∈ Set.Ioo (theta0 - delta) (theta0 + delta), fp t = 0 := by
    intro t ht
    have hnb : Set.Ioo (theta0 - delta) (theta0 + delta) ∈ nhds t :=
      Ioo_mem_nhds ht.1 ht.2
    have hev : f =ᶠ[nhds t] fun _ => c := by
      filter_upwards [hnb] with s hs using hIoo s hs
    have := (hev.hasDerivAt_iff (f' := (0:ℝ))).2 (hasDerivAt_const t c)
    exact this.unique (hf t) ▸ rfl
  -- hence `fpp` vanishes at the centre
  have hcentre : theta0 ∈ Set.Ioo (theta0 - delta) (theta0 + delta) :=
    ⟨by linarith, by linarith⟩
  have hfpp0 : fpp theta0 = 0 := by
    have hnb : Set.Ioo (theta0 - delta) (theta0 + delta) ∈ nhds theta0 :=
      Ioo_mem_nhds hcentre.1 hcentre.2
    have hev : fp =ᶠ[nhds theta0] fun _ => (0:ℝ) := by
      filter_upwards [hnb] with s hs using hfp0 s hs
    have := (hev.hasDerivAt_iff (f' := (0:ℝ))).2 (hasDerivAt_const theta0 (0:ℝ))
    exact (this.unique (hfp theta0)).symm ▸ rfl
  -- solve the linear system
  set u : ℝ := 2 * alpha * theta0 with hudef
  have hval : A * Real.cos u + B * Real.sin u = c := hIoo theta0 hcentre
  have h2 : (2 : ℝ) * alpha ≠ 0 := by
    simpa using halpha
  have hd1 : A * (-Real.sin u) + B * Real.cos u = 0 := by
    have hz := hfp0 theta0 hcentre
    simp only [hfpdef, ← hudef] at hz
    have hfac : (2 * alpha) * (A * (-Real.sin u) + B * Real.cos u) = 0 := by
      linear_combination hz
    exact (mul_eq_zero.1 hfac).resolve_left h2
  have hc0 : c = 0 := by
    have hz := hfpp0
    simp only [hfppdef, ← hudef] at hz
    have hfac : (2 * alpha) ^ 2 * (A * Real.cos u + B * Real.sin u) = 0 := by
      linear_combination -hz
    rw [hval] at hfac
    exact (mul_eq_zero.1 hfac).resolve_left (pow_ne_zero 2 h2)
  have hpyth : Real.cos u ^ 2 + Real.sin u ^ 2 = 1 := by
    rw [add_comm]; exact Real.sin_sq_add_cos_sq u
  rw [hc0] at hval
  refine ⟨?_, ?_, hc0⟩
  · linear_combination (Real.cos u) * hval - (Real.sin u) * hd1 - A * hpyth
  · linear_combination (Real.sin u) * hval + (Real.cos u) * hd1 - B * hpyth
