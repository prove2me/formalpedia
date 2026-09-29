-- Prove2me | solution 1 for zeta_ne_zero_of_mem_strip_of_abs_im_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T12:14:05.610165+00:00
-- url     : https://prove2.me/submissions/941b93f9-af41-473c-b4a2-68feb5b2bedb

/-
An explicit zero-free rectangle for the Riemann zeta function.

The main result of this file is that `ζ` has no zeros in the region

  `0 < Re s < 1`,  `|Im s| ≤ 2`,

i.e. the low-lying part of the critical strip is zero-free.  (The first nontrivial zero is at
height `≈ 14.13`, so this is a genuine — if modest — unconditional zero-free region, proved here
from scratch.)

The proof is an explicit majorisation of the entire function `Λ₀ = completedRiemannZeta₀`.
Mathlib defines `Λ₀` as the Mellin transform of a modified Jacobi theta kernel, and
`Λ s = Λ₀ s - 1 / s - 1 / (1 - s)`.  Using the exponential decay of the theta kernel one gets the
completely explicit bound `‖Λ₀ s‖ ≤ 1/8` for `0 < Re s < 1`, while
`‖1 / s + 1 / (1 - s)‖ = 1 / (‖s‖ * ‖1 - s‖) ≥ 1/5` in the rectangle.  Hence `Λ s ≠ 0` there, and
therefore `ζ s ≠ 0`.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real

namespace ZetaZeroFreeRectangle

/-- The Jacobi-theta functional-equation pair underlying Mathlib's completed zeta function. -/
noncomputable def P : WeakFEPair ℂ := hurwitzEvenFEPair 0

/-! ### Bounds for the theta kernel -/

lemma evenKernel_zero_eq_F_int {t : ℝ} (ht : 0 < t) :
    evenKernel 0 t = HurwitzKernelBounds.F_int 0 0 t := by
  have h := (hasSum_int_evenKernel 0 ht).tsum_eq
  have h2 : HurwitzKernelBounds.F_int 0 ((0 : ℝ) : UnitAddCircle) t
      = ∑' n : ℤ, HurwitzKernelBounds.f_int 0 0 t n := by
    simp only [HurwitzKernelBounds.F_int, Function.Periodic.lift_coe]
  simp only [QuotientAddGroup.mk_zero] at h2 h
  rw [h2, ← h]
  simp [HurwitzKernelBounds.f_int]

/-- Explicit bound for the theta kernel: `|θ t - 1| ≤ 2 e ^ (-π t) / (1 - e ^ (-π t))`. -/
lemma abs_evenKernel_zero_sub_one_le {t : ℝ} (ht : 0 < t) :
    |evenKernel 0 t - 1| ≤ 2 * rexp (-π * t) / (1 - rexp (-π * t)) := by
  have h1 := HurwitzKernelBounds.F_nat_zero_zero_sub_le ht
  have h2 := HurwitzKernelBounds.F_nat_zero_le (a := 1) zero_le_one ht
  have h3 : HurwitzKernelBounds.F_int 0 ((0 : ℝ) : UnitAddCircle) t
      = HurwitzKernelBounds.F_nat 0 0 t + HurwitzKernelBounds.F_nat 0 (1 - 0) t :=
    HurwitzKernelBounds.F_int_eq_of_mem_Icc 0 (by simp) ht
  simp only [QuotientAddGroup.mk_zero, sub_zero] at h3
  simp only [Real.norm_eq_abs, one_pow, mul_one] at h1 h2
  rw [evenKernel_zero_eq_F_int ht, h3,
    show HurwitzKernelBounds.F_nat 0 0 t + HurwitzKernelBounds.F_nat 0 1 t - 1
      = (HurwitzKernelBounds.F_nat 0 0 t - 1) + HurwitzKernelBounds.F_nat 0 1 t from by ring]
  calc |_| ≤ |HurwitzKernelBounds.F_nat 0 0 t - 1| + |HurwitzKernelBounds.F_nat 0 1 t| :=
        abs_add_le _ _
    _ ≤ rexp (-π * t) / (1 - rexp (-π * t)) + rexp (-π * t) / (1 - rexp (-π * t)) :=
        add_le_add h1 h2
    _ = 2 * rexp (-π * t) / (1 - rexp (-π * t)) := by ring

lemma exp_pi_ge : (20 : ℝ) ≤ rexp π := by
  have hpi : (3.14 : ℝ) < π := Real.pi_gt_d2
  have h := Real.sum_le_exp_of_nonneg (x := π) Real.pi_pos.le 6
  simp [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [pow_pos Real.pi_pos 2, pow_pos Real.pi_pos 3, pow_pos Real.pi_pos 4,
    pow_pos Real.pi_pos 5, hpi]

lemma exp_neg_pi_le : rexp (-π) ≤ 1 / 20 := by
  have h := exp_pi_ge
  have hp : (0 : ℝ) < rexp π := Real.exp_pos _
  have hx : (0 : ℝ) < rexp (-π) := Real.exp_pos _
  have hprod : rexp (-π) * rexp π = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith

/-- For `t ≥ 1` the theta kernel satisfies `|θ t - 1| ≤ (5/2) e ^ (-π t)`. -/
lemma abs_evenKernel_sub_one_le_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    |evenKernel 0 t - 1| ≤ 5 / 2 * rexp (-π * t) := by
  have hexp : rexp (-π * t) ≤ rexp (-π) := by
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_pos]
  have h20 : rexp (-π * t) ≤ 1 / 20 := le_trans hexp exp_neg_pi_le
  have hpos : 0 < rexp (-π * t) := Real.exp_pos _
  have hd : (0 : ℝ) < 1 - rexp (-π * t) := by linarith
  refine (abs_evenKernel_zero_sub_one_le (by linarith)).trans ?_
  rw [div_le_iff₀ hd]
  nlinarith

/-- The theta functional equation in the form we need. -/
lemma evenKernel_eq_of_pos {t : ℝ} (h0 : 0 < t) :
    evenKernel 0 t = t ^ (-(1 : ℝ) / 2) * evenKernel 0 (1 / t) := by
  have h := evenKernel_functional_equation 0 t
  rw [← evenKernel_eq_cosKernel_of_zero] at h
  rw [h]
  congr 1
  rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_mul h0.le]
  norm_num

/-! ### The modified kernel appearing in the Mellin transform -/

lemma f_modif_of_one_lt {t : ℝ} (ht : 1 < t) :
    P.f_modif t = ((evenKernel 0 t : ℝ) : ℂ) - 1 := by
  simp [P, WeakFEPair.f_modif, hurwitzEvenFEPair, ht, not_lt.2 ht.le, Set.indicator_of_notMem]

lemma f_modif_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    P.f_modif t = ((evenKernel 0 t : ℝ) : ℂ) - ((t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
  simp [P, WeakFEPair.f_modif, hurwitzEvenFEPair, h0, h1, not_lt.2 h1.le]
  norm_num

lemma f_modif_one : P.f_modif 1 = 0 := by
  simp [P, WeakFEPair.f_modif]

lemma norm_f_modif_le_of_one_lt {t : ℝ} (ht : 1 < t) :
    ‖P.f_modif t‖ ≤ 5 / 2 * rexp (-π * t) := by
  rw [f_modif_of_one_lt ht,
    show ((evenKernel 0 t : ℝ) : ℂ) - 1 = ((evenKernel 0 t - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_evenKernel_sub_one_le_of_one_le ht.le

lemma norm_f_modif_le_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ‖P.f_modif t‖ ≤ 5 / 2 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t) := by
  have ht1 : (1 : ℝ) ≤ 1 / t := by rw [le_div_iff₀ h0]; linarith
  have hrpow : (0 : ℝ) < t ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos h0 _
  rw [f_modif_of_lt_one h0 h1,
    show ((evenKernel 0 t : ℝ) : ℂ) - ((t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
      = ((evenKernel 0 t - t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, evenKernel_eq_of_pos h0,
    show t ^ (-(1 : ℝ) / 2) * evenKernel 0 (1 / t) - t ^ (-(1 : ℝ) / 2)
      = t ^ (-(1 : ℝ) / 2) * (evenKernel 0 (1 / t) - 1) from by ring,
    abs_mul, abs_of_pos hrpow, mul_comm (5 / 2 : ℝ), mul_assoc]
  have h := abs_evenKernel_sub_one_le_of_one_le ht1
  rw [show -π * (1 / t) = -π / t by ring] at h
  exact mul_le_mul_of_nonneg_left h hrpow.le

/-! ### The majorant and its integral -/

/-- Explicit integrable majorant for the Mellin integrand on `(0, ∞)`. -/
noncomputable def maj (t : ℝ) : ℝ :=
  if t ≤ 1 then 60 / π ^ 4 * t ^ (5 / 2 : ℝ) else 5 / 2 * rexp (-π * t)

lemma integrableOn_maj_Ioc : IntegrableOn maj (Ioc (0 : ℝ) 1) := by
  have h : IntegrableOn (fun t : ℝ => 60 / π ^ 4 * t ^ (5 / 2 : ℝ)) (Ioc (0 : ℝ) 1) :=
    ((intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) (r := 5 / 2)
      (by norm_num)).1).const_mul _
  refine h.congr_fun ?_ measurableSet_Ioc
  intro t ht
  simp [maj, ht.2]

lemma integrableOn_maj_Ioi : IntegrableOn maj (Ioi (1 : ℝ)) := by
  have h : IntegrableOn (fun t : ℝ => 5 / 2 * rexp (-π * t)) (Ioi (1 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 1 Real.pi_pos).const_mul _
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have h1 : ¬ t ≤ 1 := not_le.2 (mem_Ioi.mp ht)
  simp [maj, h1]

lemma integrableOn_maj : IntegrableOn maj (Ioi 0) := by
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  exact integrableOn_maj_Ioc.union integrableOn_maj_Ioi

lemma integral_maj_le : ∫ t in Ioi (0 : ℝ), maj t ≤ 1 / 4 := by
  have hsplit : ∫ t in Ioi (0 : ℝ), maj t
      = (∫ t in Ioc (0 : ℝ) 1, maj t) + ∫ t in Ioi (1 : ℝ), maj t := by
    rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
    exact setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi
      integrableOn_maj_Ioc integrableOn_maj_Ioi
  have h1 : ∫ t in Ioc (0 : ℝ) 1, maj t = 60 / π ^ 4 * (2 / 7) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun t : ℝ => 60 / π ^ 4 * t ^ (5 / 2 : ℝ))
      (fun t ht => by simp [maj, ht.2])]
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by norm_num))]
    norm_num
  have h2 : ∫ t in Ioi (1 : ℝ), maj t = 5 / 2 * (rexp (-π) / π) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ => 5 / 2 * rexp (-π * t))
      (fun t ht => by simp [maj, not_le.2 (mem_Ioi.mp ht)])]
    rw [integral_const_mul]
    congr 1
    have h := MeasureTheory.integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) 1 Real.pi_pos
    simp only [smul_eq_mul, mul_one] at h
    rw [show (fun t : ℝ => Real.exp (-π * t)) = (fun t : ℝ => Real.exp (-(π * t))) by
      ext t; ring_nf]
    rw [h, integral_exp_neg_Ioi]
    ring
  rw [hsplit, h1, h2]
  have hpi : (3.14 : ℝ) < π := Real.pi_gt_d2
  have hpi0 : (0 : ℝ) < π := Real.pi_pos
  have hp2 : (9.8596 : ℝ) ≤ π ^ 2 := by nlinarith
  have hp4 : (97 : ℝ) ≤ π ^ 4 := by nlinarith
  have ha : 60 / π ^ 4 * (2 / 7) ≤ 60 / 97 * (2 / 7) := by gcongr
  have hb : 5 / 2 * (rexp (-π) / π) ≤ 5 / 2 * ((1 / 20) / 3.14) := by gcongr; exact exp_neg_pi_le
  linarith

/-- `e ^ (-x) ≤ 24 / x ^ 4` for `x > 0`. -/
lemma exp_neg_le_quartic {x : ℝ} (hx : 0 < x) : rexp (-x) ≤ 24 / x ^ 4 := by
  have h4 : (0 : ℝ) < x ^ 4 := pow_pos hx 4
  have h : x ^ 4 / 24 ≤ Real.exp x := by
    have := Real.sum_le_exp_of_nonneg hx.le 5
    simp [Finset.sum_range_succ, Nat.factorial] at this
    nlinarith [this, pow_pos hx 2, pow_pos hx 3]
  rw [le_div_iff₀ h4, Real.exp_neg, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos x)]
  nlinarith

/-- The pointwise bound for the Mellin integrand of `Λ₀` in the critical strip. -/
lemma norm_integrand_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s / 2 - 1) • P.f_modif t‖ ≤ maj t := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have hre : (s / 2 - 1).re = s.re / 2 - 1 := by simp
  rw [hre]
  rcases lt_trichotomy t 1 with hlt | rfl | hgt
  · have hmaj : maj t = 60 / π ^ 4 * t ^ (5 / 2 : ℝ) := by simp [maj, hlt.le]
    rw [hmaj]
    have hq : rexp (-π / t) ≤ 24 / (π / t) ^ 4 := by
      have := exp_neg_le_quartic (x := π / t) (by positivity)
      rwa [show -(π / t) = -π / t by ring] at this
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤ t ^ (s.re / 2 - 1) * (5 / 2 * t ^ (-(1 : ℝ) / 2) * (24 / (π / t) ^ 4)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
      refine le_trans (norm_f_modif_le_of_lt_one ht hlt) ?_
      exact mul_le_mul_of_nonneg_left hq (by positivity)
    refine hstep.trans ?_
    have hpi : (0 : ℝ) < π := Real.pi_pos
    have hrw : 24 / (π / t) ^ 4 = 24 / π ^ 4 * t ^ (4 : ℝ) := by
      rw [div_pow, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    rw [hrw]
    have hcomb : t ^ (s.re / 2 - 1) * (5 / 2 * t ^ (-(1 : ℝ) / 2) * (24 / π ^ 4 * t ^ (4 : ℝ)))
        = 60 / π ^ 4 * t ^ (s.re / 2 + 5 / 2) := by
      rw [show s.re / 2 + 5 / 2 = (s.re / 2 - 1) + (-(1 : ℝ) / 2) + 4 by ring,
        Real.rpow_add ht, Real.rpow_add ht]
      ring
    rw [hcomb]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge ht hlt.le (by linarith)) (by positivity)
  · simp [f_modif_one, maj]
    positivity
  · have hmaj : maj t = 5 / 2 * rexp (-π * t) := by simp [maj, not_le.2 hgt]
    rw [hmaj]
    have h1' : t ^ (s.re / 2 - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hgt.le (by linarith)
    calc t ^ (s.re / 2 - 1) * ‖P.f_modif t‖ ≤ 1 * ‖P.f_modif t‖ := by gcongr
      _ = ‖P.f_modif t‖ := one_mul _
      _ ≤ 5 / 2 * rexp (-π * t) := norm_f_modif_le_of_one_lt hgt

/-! ### The main estimate -/

/-- **Explicit bound on the entire part of the completed zeta function.**
In the critical strip, `‖Λ₀ s‖ ≤ 1/8`. -/
theorem norm_completedRiemannZeta₀_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ‖completedRiemannZeta₀ s‖ ≤ 1 / 8 := by
  have hdef : completedRiemannZeta₀ s = mellin P.f_modif (s / 2) / 2 := rfl
  rw [hdef, norm_div, Complex.norm_ofNat]
  have hb : ‖mellin P.f_modif (s / 2)‖ ≤ ∫ t in Ioi (0 : ℝ), maj t := by
    rw [mellin]
    refine norm_integral_le_of_norm_le integrableOn_maj ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    exact norm_integrand_le h0 h1 ht
  have := hb.trans integral_maj_le
  linarith

lemma norm_mul_one_sub_le {s : ℂ} (him : |s.im| ≤ 2) (h0 : 0 < s.re) (h1 : s.re < 1) :
    ‖s‖ * ‖1 - s‖ ≤ 5 := by
  have hs : ‖s‖ ^ 2 ≤ 5 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [abs_le.1 him, sq_abs s.im]
  have hs' : ‖1 - s‖ ^ 2 ≤ 5 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    nlinarith [abs_le.1 him, sq_abs s.im]
  nlinarith [norm_nonneg s, norm_nonneg (1 - s)]

/-- **The completed zeta function has no zeros in the low-lying rectangle.** -/
theorem completedRiemannZeta_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : |s.im| ≤ 2) : completedRiemannZeta s ≠ 0 := by
  intro hz
  have hs0 : s ≠ 0 := fun h => by simp [h] at h0
  have hs1 : s ≠ 1 := by rintro rfl; simp at h1
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  have key : completedRiemannZeta₀ s = 1 / s + 1 / (1 - s) := by
    have h := completedRiemannZeta_eq s
    rw [hz] at h
    linear_combination -h
  have heq : (1 : ℂ) / s + 1 / (1 - s) = 1 / (s * (1 - s)) := by
    field_simp
    ring
  rw [heq] at key
  have hnorm : ‖completedRiemannZeta₀ s‖ = 1 / (‖s‖ * ‖1 - s‖) := by
    rw [key, norm_div, norm_one, norm_mul]
  have hb := norm_completedRiemannZeta₀_le h0 h1
  rw [hnorm] at hb
  have hpos : 0 < ‖s‖ * ‖1 - s‖ := mul_pos (norm_pos_iff.2 hs0) (norm_pos_iff.2 h1s)
  have h5 := norm_mul_one_sub_le him h0 h1
  rw [div_le_iff₀ hpos] at hb
  linarith

/-- **An explicit zero-free rectangle for the Riemann zeta function.**
`ζ` has no zero `s` with `0 < Re s < 1` and `|Im s| ≤ 2`. -/
theorem riemannZeta_ne_zero_of_abs_im_le_two {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : |s.im| ≤ 2) : riemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at h0
  rw [riemannZeta_def_of_ne_zero hs0]
  intro hz
  rcases div_eq_zero_iff.mp hz with h | h
  · exact completedRiemannZeta_ne_zero h0 h1 him h
  · exact Complex.Gammaℝ_ne_zero_of_re_pos h0 h

/-- **Reduction of the half-plane form of the Riemann hypothesis.**
Thanks to the zero-free rectangle above (and to the classical non-vanishing of `ζ` on
`Re s ≥ 1`), the statement "`ζ` has no zeros with `Re s > 1/2`" — which is equivalent to the
Riemann hypothesis — follows from the a priori weaker statement about zeros of height
`|Im s| > 2` only. -/
theorem zeta_ne_zero_of_half_lt_re_of_high_zeros_free
    (H : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → 2 < |s.im| → riemannZeta s ≠ 0)
    (s : ℂ) (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  rcases le_or_gt 1 s.re with h | h
  · exact riemannZeta_ne_zero_of_one_le_re h
  · rcases le_or_gt |s.im| 2 with h2 | h2
    · exact riemannZeta_ne_zero_of_abs_im_le_two (by linarith) h h2
    · exact H s hs h h2

end ZetaZeroFreeRectangle

theorem solution (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (him : |s.im| ≤ 2) :
    riemannZeta s ≠ 0 :=
  ZetaZeroFreeRectangle.riemannZeta_ne_zero_of_abs_im_le_two h0 h1 him
