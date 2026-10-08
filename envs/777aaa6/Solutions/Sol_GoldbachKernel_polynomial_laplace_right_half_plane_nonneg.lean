-- Prove2me | solution 1 for GoldbachKernel_polynomial_laplace_right_half_plane_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T06:59:54.133897+00:00
-- url     : https://prove2.me/submissions/97776002-7d2b-4bf7-a15f-37e52df22424

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

open MeasureTheory
set_option autoImplicit false

-- Local prerequisite for a future all-frequency comparison; no inequality is asserted.
theorem goldbach_complex_laplace_closed_form (z : ℂ) (hz : z ≠ 0) :
    (∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-z*(u:ℂ))) =
      (16*z^5-40*z^3+60*z^2-60+60*Complex.exp (-2*z)*(z+1)^2)/(15*z^6) := by
  let a0 : ℂ := -16/(15*z)+8/(3*z^3)-4/z^4+4/z^6
  let a1 : ℂ := 8/(3*z^2)-4/z^3+4/z^5
  let a2 : ℂ := 4/(3*z)-2/z^2+2/z^4
  let a3 : ℂ := -2/(3*z)+2/(3*z^3)
  let a4 : ℂ := 1/(6*z^2)
  let a5 : ℂ := 1/(30*z)
  let Q : ℂ → ℂ := fun u => a0+a1*u+a2*u^2+a3*u^3+a4*u^4+a5*u^5
  have hQ (u : ℂ) : HasDerivAt Q (a1+2*a2*u+3*a3*u^2+4*a4*u^3+5*a5*u^4) u := by
    convert (((((hasDerivAt_const u a0).add ((hasDerivAt_id u).const_mul a1)).add
      ((hasDerivAt_pow 2 u).const_mul a2)).add ((hasDerivAt_pow 3 u).const_mul a3)).add
      ((hasDerivAt_pow 4 u).const_mul a4)).add ((hasDerivAt_pow 5 u).const_mul a5) using 1
    dsimp [Q]
    ring
  have hd (u : ℂ) : HasDerivAt (fun v => Q v*Complex.exp (-z*v))
      (((2-u)^3*(4+6*u+u^2)/30)*Complex.exp (-z*u)) u := by
    have he := (Complex.hasDerivAt_exp (-z*u)).comp u ((hasDerivAt_id u).const_mul (-z))
    convert (hQ u).mul he using 1
    dsimp [Q,a0,a1,a2,a3,a4,a5]
    field_simp
    ring
  have hreal (u : ℝ) : HasDerivAt (fun v : ℝ => Q (v:ℂ)*Complex.exp (-z*(v:ℂ)))
      (((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*Complex.exp (-z*(u:ℂ))) u := by
    simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_ofNat] using
      (hd (u:ℂ)).comp_ofReal
  have hint : IntervalIntegrable
      (fun u : ℝ => (((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*Complex.exp (-z*(u:ℂ))))
      volume 0 2 := by
    have hcont : Continuous
        (fun u : ℝ => (((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*Complex.exp (-z*(u:ℂ)))) := by
      fun_prop
    exact hcont.intervalIntegrable (μ := volume) 0 2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hreal u) hint]
  dsimp [Q,a0,a1,a2,a3,a4,a5]
  have he : -z*2 = -2*z := by ring
  norm_num only [Complex.ofReal_ofNat]
  rw [he]
  norm_num
  field_simp
  ring

#print axioms goldbach_complex_laplace_closed_form

-- The rational expression above has an apparent singularity; handle its origin separately.
theorem goldbach_complex_laplace_at_zero :
    (∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-(0:ℂ)*(u:ℂ))) = (8/9:ℂ) := by
  simp only [neg_zero, zero_mul, Complex.exp_zero, mul_one]
  let P : ℝ → ℝ := fun u => 16*u/15-4*u^3/9+u^4/6-u^6/180
  have hP (u : ℝ) : HasDerivAt P (((2-u)^3*(4+6*u+u^2)/30):ℝ) u := by
    convert ((((hasDerivAt_id u).const_mul 16).div_const 15).sub
      (((hasDerivAt_pow 3 u).const_mul 4).div_const 9)).add
      ((hasDerivAt_pow 4 u).div_const 6) |>.sub
      ((hasDerivAt_pow 6 u).div_const 180) using 1
    dsimp [P]
    ring
  have hint : IntervalIntegrable
      (fun u : ℝ => ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)) volume 0 2 := by
    have hcont : Continuous (fun u : ℝ => ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)) := by
      fun_prop
    exact hcont.intervalIntegrable (μ := volume) 0 2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => (hP u).ofReal_comp) hint]
  norm_num [P]
  rfl

#print axioms goldbach_complex_laplace_at_zero

theorem goldbach_complex_laplace_imaginary_axis (t : ℝ) (ht : t ≠ 0) :
    ((∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-((t:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re =
      8*(t*Real.cos t-Real.sin t)^2/t^6 := by
  rw [goldbach_complex_laplace_closed_form ((t:ℂ)*Complex.I)
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero)]
  norm_num [Complex.div_re, Complex.normSq_apply, pow_succ, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.exp_re, Complex.exp_im, Real.cos_neg, Real.sin_neg]
  rw [Real.cos_two_mul, Real.sin_two_mul]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq t]

#print axioms goldbach_complex_laplace_imaginary_axis

theorem goldbach_complex_laplace_imaginary_axis_nonneg (t : ℝ) :
    0 ≤ ((∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-((t:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re := by
  by_cases ht : t = 0
  · subst t
    simp only [Complex.ofReal_zero, zero_mul]
    rw [goldbach_complex_laplace_at_zero]
    norm_num
  · rw [goldbach_complex_laplace_imaginary_axis t ht]
    positivity

#print axioms goldbach_complex_laplace_imaginary_axis_nonneg

theorem goldbach_complex_laplace_right_half_plane_norm (z : ℂ) (hz : 0 ≤ z.re) :
    ‖∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-z*(u:ℂ))‖ ≤ (8/9:ℝ) := by
  let g : ℝ → ℝ := fun u => (2-u)^3*(4+6*u+u^2)/30
  have hg : Continuous g := by fun_prop
  have hgc : IntervalIntegrable (fun u : ℝ => (g u:ℂ)) volume (0:ℝ) 2 :=
    (Complex.continuous_ofReal.comp hg).intervalIntegrable (μ := volume) 0 2
  have hmap := Complex.reCLM.intervalIntegral_comp_comm hgc
  have hmass : (∫ u in (0:ℝ)..2, g u) = (8/9:ℝ) := by
    have hzero := congrArg Complex.re goldbach_complex_laplace_at_zero
    simp only [neg_zero, zero_mul, Complex.exp_zero, mul_one] at hzero
    norm_num at hzero
    calc
      _ = ((∫ u in (0:ℝ)..2, (g u:ℂ)) : ℂ).re := by exact hmap
      _ = _ := by simpa [g] using hzero
  have hnorm (u : ℝ) (hu : u ∈ Set.Ioc (0:ℝ) 2) :
      ‖(g u:ℂ)*Complex.exp (-z*(u:ℂ))‖ ≤ g u := by
    have hgp : 0 ≤ g u := by
      dsimp [g]
      apply div_nonneg
      · apply mul_nonneg
        · exact pow_nonneg (by linarith [hu.2]) _
        · nlinarith [hu.1, sq_nonneg u]
      · norm_num
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgp,
      Complex.norm_exp]
    apply mul_le_of_le_one_right hgp
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) hu.1.le
  calc
    _ ≤ ∫ u in (0:ℝ)..2, g u :=
      intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        (Filter.Eventually.of_forall hnorm) (hg.intervalIntegrable (μ := volume) 0 2)
    _ = _ := hmass

#print axioms goldbach_complex_laplace_right_half_plane_norm

private noncomputable def goldbachG (z : ℂ) : ℂ :=
  ∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*Complex.exp (-z*(u:ℂ))

private lemma goldbachG_diffCont : DiffContOnCl ℂ goldbachG {z : ℂ | 0 < z.re} := by
  constructor
  · intro z hz
    have hz0 : z ≠ 0 := by intro h; subst z; simp at hz
    let H : ℂ → ℂ := fun z =>
      (16*z^5-40*z^3+60*z^2-60+60*Complex.exp (-2*z)*(z+1)^2)/(15*z^6)
    have hden : (15:ℂ)*z^6 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hz0)
    have hH : DifferentiableAt ℂ H z := by dsimp [H]; fun_prop (disch := assumption)
    have heq : goldbachG =ᶠ[nhds z] H := by
      filter_upwards [eventually_ne_nhds hz0] with w hw
      exact goldbach_complex_laplace_closed_form w hw
    exact (hH.congr_of_eventuallyEq heq).differentiableWithinAt
  · rw [Complex.closure_setOf_lt_re]
    apply continuousOn_iff_continuous_restrict.mpr
    let g : ℝ → ℝ := fun u => (2-u)^3*(4+6*u+u^2)/30
    have hg : Continuous g := by fun_prop
    apply intervalIntegral.continuous_of_dominated_interval (bound := g)
    · intro z
      have hc : Continuous (fun u : ℝ => (g u:ℂ)*Complex.exp (-(z.val)*(u:ℂ))) := by
        fun_prop
      exact hc.aestronglyMeasurable
    · intro z
      apply Filter.Eventually.of_forall
      intro u hu
      have hui : u ∈ Set.Ioc (0:ℝ) 2 := by simpa using hu
      have hgp : 0 ≤ g u := by
        dsimp [g]
        apply div_nonneg
        · apply mul_nonneg
          · exact pow_nonneg (by linarith [hui.2]) _
          · nlinarith [hui.1, sq_nonneg u]
        · norm_num
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgp,
        Complex.norm_exp]
      apply mul_le_of_le_one_right hgp
      apply Real.exp_le_one_iff.mpr
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr z.property) hui.1.le
    · exact hg.intervalIntegrable (μ := volume) 0 2
    · apply Filter.Eventually.of_forall
      intro u _
      fun_prop

theorem solution (z : ℂ) (hz : 0 ≤ z.re) :
    0 ≤ ((∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-z*(u:ℂ))) : ℂ).re := by
  let f : ℂ → ℂ := fun z => Complex.exp (-goldbachG z)
  have hd : DiffContOnCl ℂ f {z : ℂ | 0 < z.re} :=
    Complex.differentiable_exp.comp_diffContOnCl goldbachG_diffCont.neg
  have hbound (w : ℂ) (hw : 0 ≤ w.re) : ‖f w‖ ≤ Real.exp (8/9) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hnorm := goldbach_complex_laplace_right_half_plane_norm w hw
    have hre := (neg_le_abs (goldbachG w).re).trans (Complex.abs_re_le_norm (goldbachG w))
    change -(goldbachG w).re ≤ 8/9
    exact hre.trans hnorm
  have hexp : ∃ c < (2:ℝ), ∃ B : ℝ,
      f =O[Bornology.cobounded ℂ ⊓ Filter.principal {z : ℂ | 0 < z.re}]
        (fun z => Real.exp (B*‖z‖^c)) := by
    refine ⟨0, by norm_num, 0, Asymptotics.IsBigO.of_bound (Real.exp (8/9)) ?_⟩
    apply Filter.eventually_inf_principal.mpr
    apply Filter.Eventually.of_forall
    intro w hw
    simpa using hbound w hw.le
  have hre : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun x : ℝ => ‖f (x:ℂ)‖) := by
    refine ⟨Real.exp (8/9), ?_⟩
    change ∀ᶠ x : ℝ in Filter.atTop, ‖f (x:ℂ)‖ ≤ Real.exp (8/9)
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with x hx
    exact hbound (x:ℂ) hx
  have him (t : ℝ) : ‖f ((t:ℂ)*Complex.I)‖ ≤ (1:ℝ) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (goldbach_complex_laplace_imaginary_axis_nonneg t)
  have h := PhragmenLindelof.right_half_plane_of_bounded_on_real hd hexp hre him hz
  change ‖Complex.exp (-goldbachG z)‖ ≤ (1:ℝ) at h
  rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff] at h
  exact neg_nonpos.mp h

#print axioms solution
