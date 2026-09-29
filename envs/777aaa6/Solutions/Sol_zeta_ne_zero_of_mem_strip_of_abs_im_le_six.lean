-- Prove2me | solution 1 for zeta_ne_zero_of_mem_strip_of_abs_im_le_six
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T13:54:29.775539+00:00
-- url     : https://prove2.me/submissions/7ab19408-190a-439f-81f8-63e983ebb00b

/-
An explicit zero-free rectangle for the Riemann zeta function:
`ζ s ≠ 0` whenever `0 < Re s < 1` and `|Im s| ≤ 6`.

Self-contained solution file: it re-proves, from Mathlib only, the bounds on the Jacobi theta
kernel that Mathlib's completed zeta function is built from.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real

namespace ZetaSix

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
/-! ### Numerical input: `e ^ π ≥ 23` -/

lemma exp_pi_ge_23 : (23 : ℝ) ≤ rexp π := by
  have h1 : (0.7853 : ℝ) < π / 4 := by nlinarith [Real.pi_gt_d4]
  have hp : (0 : ℝ) < π / 4 := by positivity
  have h2 : (2.19 : ℝ) ≤ rexp (π / 4) := by
    have h := Real.sum_le_exp_of_nonneg (x := π / 4) hp.le 6
    simp [Finset.sum_range_succ, Nat.factorial] at h
    nlinarith [h1, pow_pos hp 2, pow_pos hp 3, pow_pos hp 4, pow_pos hp 5]
  have h3 : (rexp (π / 4)) ^ 4 = rexp π := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h4 : (2.19 : ℝ) ^ 4 ≤ (rexp (π / 4)) ^ 4 := by gcongr
  rw [← h3]; nlinarith [h4]

lemma exp_neg_pi_le_23 : rexp (-π) ≤ 1 / 23 := by
  have h := exp_pi_ge_23
  have hprod : rexp (-π) * rexp π = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-π), Real.exp_pos π]
/-! ### The theta kernel with the sharper constant `21/10` -/

lemma abs_evenKernel_sub_one_le_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    |evenKernel 0 t - 1| ≤ 21 / 10 * rexp (-π * t) := by
  have hexp : rexp (-π * t) ≤ rexp (-π) := by
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_pos]
  have h23 : rexp (-π * t) ≤ 1 / 23 := le_trans hexp exp_neg_pi_le_23
  have hpos : 0 < rexp (-π * t) := Real.exp_pos _
  have hd : (0 : ℝ) < 1 - rexp (-π * t) := by linarith
  refine (abs_evenKernel_zero_sub_one_le (by linarith)).trans ?_
  rw [div_le_iff₀ hd]
  nlinarith

lemma norm_f_modif_le_of_one_lt {t : ℝ} (ht : 1 < t) :
    ‖P.f_modif t‖ ≤ 21 / 10 * rexp (-π * t) := by
  rw [f_modif_of_one_lt ht,
    show ((evenKernel 0 t : ℝ) : ℂ) - 1 = ((evenKernel 0 t - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_evenKernel_sub_one_le_of_one_le ht.le

lemma norm_f_modif_le_of_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ‖P.f_modif t‖ ≤ 21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t) := by
  have ht1 : (1 : ℝ) ≤ 1 / t := by rw [le_div_iff₀ h0]; linarith
  have hrpow : (0 : ℝ) < t ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos h0 _
  rw [f_modif_of_lt_one h0 h1,
    show ((evenKernel 0 t : ℝ) : ℂ) - ((t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
      = ((evenKernel 0 t - t ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, evenKernel_eq_of_pos h0,
    show t ^ (-(1 : ℝ) / 2) * evenKernel 0 (1 / t) - t ^ (-(1 : ℝ) / 2)
      = t ^ (-(1 : ℝ) / 2) * (evenKernel 0 (1 / t) - 1) from by ring,
    abs_mul, abs_of_pos hrpow, mul_comm (21 / 10 : ℝ), mul_assoc]
  have h := abs_evenKernel_sub_one_le_of_one_le ht1
  rw [show -π * (1 / t) = -π / t by ring] at h
  exact mul_le_mul_of_nonneg_left h hrpow.le

/-! ### The tail integral `J = ∫_1^∞ u^{-1/2} e^{-π u} du` -/

/-- `∫_0^∞ x^k e^{-π x} dx = k! / π^{k+1}`. -/
lemma integral_pow_mul_exp (k : ℕ) :
    (∫ x in Ioi (0 : ℝ), x ^ k * rexp (-π * x)) = (Nat.factorial k) / π ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := π) (by positivity)
    Real.pi_pos
  have hc : (∫ x in Ioi (0 : ℝ), x ^ ((k : ℝ) + 1 - 1) * rexp (-(π * x)))
      = ∫ x in Ioi (0 : ℝ), x ^ k * rexp (-π * x) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    rw [show ((k : ℝ) + 1 - 1) = (k : ℝ) by ring, Real.rpow_natCast]
    ring_nf
  rw [hc, Real.Gamma_nat_eq_factorial k,
    show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at h
  rw [h, div_pow, one_pow]
  field_simp

/-- Translation of an integral over `(1,∞)` to one over `(0,∞)`. -/
lemma integral_Ioi_one_shift (g : ℝ → ℝ) :
    (∫ u in Ioi (1 : ℝ), g u) = ∫ x in Ioi (0 : ℝ), g (x + 1) := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_add_right_eq_self (fun x => (Ioi (1 : ℝ)).indicator g x) 1]
  congr 1
  ext x
  by_cases h : (0 : ℝ) < x
  · rw [Set.indicator_of_mem (by simp; linarith : x + 1 ∈ Ioi (1 : ℝ)),
      Set.indicator_of_mem (by simpa using h)]
  · rw [Set.indicator_of_notMem (by simp; linarith [not_lt.1 h] : x + 1 ∉ Ioi (1 : ℝ)),
      Set.indicator_of_notMem (by simpa using h)]

lemma integrableOn_pow_mul_exp (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * rexp (-π * x)) (Ioi 0) := by
  have hg : IntegrableOn (fun y : ℝ => rexp (-y) * y ^ ((k : ℝ) + 1 - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by positivity)
  have hs := (integrableOn_Ioi_comp_mul_left_iff
    (fun y : ℝ => rexp (-y) * y ^ ((k : ℝ) + 1 - 1)) 0 Real.pi_pos).mpr (by simpa using hg)
  have hc : IntegrableOn
      (fun x : ℝ => (π ^ k)⁻¹ * (rexp (-(π * x)) * (π * x) ^ ((k : ℝ) + 1 - 1))) (Ioi 0) :=
    hs.const_mul _
  refine hc.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := hx
  rw [show ((k : ℝ) + 1 - 1) = (k : ℝ) by ring, Real.mul_rpow Real.pi_pos.le hx0.le,
    Real.rpow_natCast, Real.rpow_natCast]
  have hne : (π : ℝ) ^ k ≠ 0 := by positivity
  field_simp

/-- The elementary upper bound `u^{-1/2} ≤ 1 - (u-1)/2 + 3(u-1)²/8` for `u ≥ 1`. -/
lemma rpow_neg_half_le_poly {u : ℝ} (hu : 1 ≤ u) :
    u ^ (-(1 : ℝ) / 2) ≤ 1 - (u - 1) / 2 + 3 * (u - 1) ^ 2 / 8 := by
  have hu0 : (0 : ℝ) < u := by linarith
  set x := u - 1 with hxdef
  have hx0 : 0 ≤ x := by simp [hxdef]; linarith
  set p : ℝ := 1 - x / 2 + 3 * x ^ 2 / 8 with hp
  have hppos : 0 < p := by rw [hp]; nlinarith [sq_nonneg (x - 2 / 3)]
  have hux : u = 1 + x := by rw [hxdef]; ring
  have hkey : 1 ≤ p ^ 2 * u := by
    rw [hux, hp]
    nlinarith [mul_nonneg (pow_nonneg hx0 3) (sq_nonneg (x - 5 / 6)), pow_nonneg hx0 3]
  have hs : (0 : ℝ) < u ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hu0 _
  have hs2 : (u ^ ((1 : ℝ) / 2)) ^ 2 = u := by
    rw [← Real.rpow_natCast (u ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul hu0.le,
      show (1 : ℝ) / 2 * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hone : 1 ≤ p * u ^ ((1 : ℝ) / 2) := by
    nlinarith [mul_pos hppos hs, hkey, hs2]
  have hinv : u ^ (-(1 : ℝ) / 2) = (u ^ ((1 : ℝ) / 2))⁻¹ := by
    rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg hu0.le]
  rw [hinv, inv_le_iff_one_le_mul₀ hs]
  linarith [hone, mul_comm p (u ^ ((1 : ℝ) / 2))]

lemma integrableOn_J : IntegrableOn (fun u : ℝ => u ^ (-(1 : ℝ) / 2) * rexp (-π * u)) (Ioi 1) := by
  have hint : IntegrableOn (fun u : ℝ => rexp (-π * u)) (Ioi (1 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 1 Real.pi_pos).congr_fun (fun t _ => by ring_nf) measurableSet_Ioi
  refine Integrable.mono' hint ?_ ?_
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (1 : ℝ)))] with u hu
    have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
    have hle : u ^ (-(1 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
    have hpos : (0 : ℝ) < u ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith [Real.exp_pos (-π * u)]

lemma integrableOn_poly_exp :
    IntegrableOn (fun u : ℝ => (1 - (u - 1) / 2 + 3 * (u - 1) ^ 2 / 8) * rexp (-π * u))
      (Ioi 1) := by
  have h0 := (integrableOn_pow_mul_exp 0).mono_set (Ioi_subset_Ioi zero_le_one)
  have h1 := (integrableOn_pow_mul_exp 1).mono_set (Ioi_subset_Ioi zero_le_one)
  have h2 := (integrableOn_pow_mul_exp 2).mono_set (Ioi_subset_Ioi zero_le_one)
  have hcomb : IntegrableOn (fun x : ℝ => 15 / 8 * (x ^ 0 * rexp (-π * x))
      - 5 / 4 * (x ^ 1 * rexp (-π * x)) + 3 / 8 * (x ^ 2 * rexp (-π * x))) (Ioi 1) :=
    ((h0.const_mul (15 / 8)).sub (h1.const_mul (5 / 4))).add (h2.const_mul (3 / 8))
  exact hcomb.congr_fun (fun x _ => by ring) measurableSet_Ioi

/-- The value of the polynomial comparison integral. -/
lemma integral_poly_exp :
    (∫ u in Ioi (1 : ℝ), (1 - (u - 1) / 2 + 3 * (u - 1) ^ 2 / 8) * rexp (-π * u))
      = rexp (-π) * (1 / π - 1 / (2 * π ^ 2) + 3 / (4 * π ^ 3)) := by
  rw [integral_Ioi_one_shift]
  have hcongr : (∫ x in Ioi (0 : ℝ),
        (1 - (x + 1 - 1) / 2 + 3 * (x + 1 - 1) ^ 2 / 8) * rexp (-π * (x + 1)))
      = ∫ x in Ioi (0 : ℝ), rexp (-π) * (1 : ℝ) * (x ^ 0 * rexp (-π * x))
          - rexp (-π) * (1 / 2) * (x ^ 1 * rexp (-π * x))
          + rexp (-π) * (3 / 8) * (x ^ 2 * rexp (-π * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [show -π * (x + 1) = -π + -π * x by ring, Real.exp_add]
    ring
  have hf : IntegrableOn (fun x : ℝ => rexp (-π) * (1 : ℝ) * (x ^ 0 * rexp (-π * x))
      - rexp (-π) * (1 / 2) * (x ^ 1 * rexp (-π * x))) (Ioi 0) := by
    simpa using ((integrableOn_pow_mul_exp 0).const_mul (rexp (-π) * 1)).sub
      ((integrableOn_pow_mul_exp 1).const_mul (rexp (-π) * (1 / 2)))
  have hg : IntegrableOn
      (fun x : ℝ => rexp (-π) * (3 / 8) * (x ^ 2 * rexp (-π * x))) (Ioi 0) := by
    simpa using (integrableOn_pow_mul_exp 2).const_mul (rexp (-π) * (3 / 8))
  have hf0 : IntegrableOn
      (fun x : ℝ => rexp (-π) * (1 : ℝ) * (x ^ 0 * rexp (-π * x))) (Ioi 0) := by
    simpa using (integrableOn_pow_mul_exp 0).const_mul (rexp (-π) * 1)
  have hf1 : IntegrableOn
      (fun x : ℝ => rexp (-π) * (1 / 2) * (x ^ 1 * rexp (-π * x))) (Ioi 0) := by
    simpa using (integrableOn_pow_mul_exp 1).const_mul (rexp (-π) * (1 / 2))
  rw [hcongr, integral_add hf hg, integral_sub hf0 hf1, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_pow_mul_exp 0, integral_pow_mul_exp 1, integral_pow_mul_exp 2]
  have hpi : (0 : ℝ) < π := Real.pi_pos
  simp only [Nat.factorial]
  push_cast
  field_simp
  ring

/-- **The tail integral is at most `0.01275`.** -/
lemma J_le : (∫ u in Ioi (1 : ℝ), u ^ (-(1 : ℝ) / 2) * rexp (-π * u)) ≤ 0.01275 := by
  have hmono : (∫ u in Ioi (1 : ℝ), u ^ (-(1 : ℝ) / 2) * rexp (-π * u))
      ≤ ∫ u in Ioi (1 : ℝ), (1 - (u - 1) / 2 + 3 * (u - 1) ^ 2 / 8) * rexp (-π * u) := by
    refine setIntegral_mono_on integrableOn_J integrableOn_poly_exp measurableSet_Ioi ?_
    intro u hu
    exact mul_le_mul_of_nonneg_right (rpow_neg_half_le_poly (le_of_lt hu)) (Real.exp_pos _).le
  refine hmono.trans ?_
  rw [integral_poly_exp]
  have hlo : (3.1415 : ℝ) < π := Real.pi_gt_d4
  have hhi : π < 3.1416 := Real.pi_lt_d4
  have hpi0 : (0 : ℝ) < π := Real.pi_pos
  have hkey : 1 / π - 1 / (2 * π ^ 2) + 3 / (4 * π ^ 3)
      = (4 * π ^ 2 - 2 * π + 3) / (4 * π ^ 3) := by field_simp; ring
  have hb : 1 / π - 1 / (2 * π ^ 2) + 3 / (4 * π ^ 3) ≤ 0.292 := by
    rw [hkey, div_le_iff₀ (by positivity)]
    nlinarith [pow_pos hpi0 2, pow_pos hpi0 3, hlo, hhi]
  have hpos : (0 : ℝ) ≤ 1 / π - 1 / (2 * π ^ 2) + 3 / (4 * π ^ 3) := by
    rw [hkey]
    have : (0 : ℝ) < 4 * π ^ 2 - 2 * π + 3 := by nlinarith [pow_pos hpi0 2]
    positivity
  calc rexp (-π) * (1 / π - 1 / (2 * π ^ 2) + 3 / (4 * π ^ 3))
      ≤ (1 / 23) * (1 / π - 1 / (2 * π ^ 2) + 3 / (4 * π ^ 3)) :=
        mul_le_mul_of_nonneg_right exp_neg_pi_le_23 hpos
    _ ≤ (1 / 23) * 0.292 := by gcongr
    _ ≤ 0.01275 := by norm_num

/-! ### The majorant -/

/-- Integrable majorant for the Mellin integrand of `Λ₀` on `(0, ∞)`, valid uniformly for
`0 < Re s < 1`. -/
noncomputable def maj (t : ℝ) : ℝ :=
  if t ≤ 1 then 21 / 10 * (t ^ (-3 / 2 : ℝ) * rexp (-π / t))
  else 21 / 10 * (t ^ (-(1 : ℝ) / 2) * rexp (-π * t))

/-- The kernel of the substituted integral: `u^{-1/2} e^{-π u}` cut off below `1`. -/
private noncomputable def gInd : ℝ → ℝ :=
  Set.indicator (Ioi 1) fun u => u ^ (-(1 : ℝ) / 2) * rexp (-π * u)

private lemma gInd_integrableOn : IntegrableOn gInd (Ioi (0 : ℝ)) := by
  rw [gInd]
  exact (integrableOn_J.integrable_indicator measurableSet_Ioi).integrableOn

private lemma integral_gInd : (∫ y in Ioi (0 : ℝ), gInd y)
    = ∫ u in Ioi (1 : ℝ), u ^ (-(1 : ℝ) / 2) * rexp (-π * u) := by
  rw [gInd, MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi]
  norm_num

private lemma cov_ptwise (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))
      = (Ioo (0 : ℝ) 1).indicator (fun x => x ^ (-3 / 2 : ℝ) * rexp (-π / x)) x := by
  have hx0 : 0 < x := hx
  have hinv : x ^ (-1 : ℝ) = x⁻¹ := by rw [Real.rpow_neg_one]
  rcases lt_or_ge x 1 with h | h
  · have h1 : (1 : ℝ) < x⁻¹ := by rw [lt_inv_comm₀ (by norm_num) hx0]; simpa using h
    rw [Set.indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from ⟨hx0, h⟩), gInd, hinv,
      Set.indicator_of_mem (mem_Ioi.mpr h1)]
    have hd : -π * x⁻¹ = -π / x := by field_simp
    have hpow : (x⁻¹) ^ (-(1 : ℝ) / 2) = x ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_neg_one x, ← Real.rpow_mul hx0.le]
      norm_num
    rw [hd, hpow, smul_eq_mul]
    have hxx : x ^ ((-1 : ℝ) - 1) * x ^ ((1 : ℝ) / 2) = x ^ (-3 / 2 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    rw [show |(-1 : ℝ)| = 1 by norm_num, one_mul, ← mul_assoc, hxx]
  · have h1 : x⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; exact h
    rw [Set.indicator_of_notMem (by simp; intro _; exact h), gInd, hinv,
      Set.indicator_of_notMem (by simp [not_lt.2 h1])]
    simp

lemma integrableOn_inner :
    IntegrableOn (fun x : ℝ => x ^ (-3 / 2 : ℝ) * rexp (-π / x)) (Ioc (0 : ℝ) 1) := by
  have h1 : IntegrableOn
      (fun x : ℝ => (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))) (Ioi 0) :=
    (MeasureTheory.integrableOn_Ioi_comp_rpow_iff gInd (by norm_num : (-1 : ℝ) ≠ 0)).mpr
      gInd_integrableOn
  have h2 : IntegrableOn
      ((Ioo (0 : ℝ) 1).indicator fun x => x ^ (-3 / 2 : ℝ) * rexp (-π / x)) (Ioi 0) :=
    h1.congr_fun cov_ptwise measurableSet_Ioi
  have h3 := (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mp h2
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioo,
    show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at h3
  rw [IntegrableOn, ← MeasureTheory.Measure.restrict_congr_set
    (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact h3

lemma integral_inner : (∫ x in Ioc (0 : ℝ) 1, x ^ (-3 / 2 : ℝ) * rexp (-π / x))
    = ∫ u in Ioi (1 : ℝ), u ^ (-(1 : ℝ) / 2) * rexp (-π * u) := by
  have hcov := MeasureTheory.integral_comp_rpow_Ioi gInd (by norm_num : (-1 : ℝ) ≠ 0)
  rw [integral_gInd] at hcov
  rw [setIntegral_congr_fun measurableSet_Ioi cov_ptwise] at hcov
  rw [MeasureTheory.integral_indicator measurableSet_Ioo, Measure.restrict_restrict
    measurableSet_Ioo, show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at hcov
  rw [← MeasureTheory.Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact hcov

lemma integrableOn_maj_Ioc : IntegrableOn maj (Ioc (0 : ℝ) 1) := by
  have h : IntegrableOn (fun x : ℝ => 21 / 10 * (x ^ (-3 / 2 : ℝ) * rexp (-π / x)))
      (Ioc (0 : ℝ) 1) := integrableOn_inner.const_mul (21 / 10)
  refine h.congr_fun ?_ measurableSet_Ioc
  intro t ht
  simp [maj, ht.2]

lemma integrableOn_maj_Ioi : IntegrableOn maj (Ioi (1 : ℝ)) := by
  have h : IntegrableOn (fun t : ℝ => 21 / 10 * (t ^ (-(1 : ℝ) / 2) * rexp (-π * t)))
      (Ioi (1 : ℝ)) := integrableOn_J.const_mul (21 / 10)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  simp [maj, not_le.2 (mem_Ioi.mp ht)]

lemma integrableOn_maj : IntegrableOn maj (Ioi 0) := by
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  exact integrableOn_maj_Ioc.union integrableOn_maj_Ioi

lemma integral_maj_le : ∫ t in Ioi (0 : ℝ), maj t ≤ 0.0536 := by
  have hsplit : ∫ t in Ioi (0 : ℝ), maj t
      = (∫ t in Ioc (0 : ℝ) 1, maj t) + ∫ t in Ioi (1 : ℝ), maj t := by
    rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
    exact setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi
      integrableOn_maj_Ioc integrableOn_maj_Ioi
  have h1 : ∫ t in Ioc (0 : ℝ) 1, maj t
      = 21 / 10 * ∫ u in Ioi (1 : ℝ), u ^ (-(1 : ℝ) / 2) * rexp (-π * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (g := fun t : ℝ => 21 / 10 * (t ^ (-3 / 2 : ℝ) * rexp (-π / t)))
      (fun t ht => by simp [maj, ht.2]), integral_const_mul, integral_inner]
  have h2 : ∫ t in Ioi (1 : ℝ), maj t
      = 21 / 10 * ∫ u in Ioi (1 : ℝ), u ^ (-(1 : ℝ) / 2) * rexp (-π * u) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun t : ℝ => 21 / 10 * (t ^ (-(1 : ℝ) / 2) * rexp (-π * t)))
      (fun t ht => by simp [maj, not_le.2 (mem_Ioi.mp ht)]), integral_const_mul]
  rw [hsplit, h1, h2]
  have hJ := J_le
  linarith

/-! ### The improved bound on `Λ₀` and the rectangle of height 6 -/

lemma norm_integrand_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s / 2 - 1) • P.f_modif t‖ ≤ maj t := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    show (s / 2 - 1).re = s.re / 2 - 1 by simp]
  rcases lt_trichotomy t 1 with hlt | rfl | hgt
  · have hmaj : maj t = 21 / 10 * (t ^ (-3 / 2 : ℝ) * rexp (-π / t)) := by simp [maj, hlt.le]
    rw [hmaj]
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤ t ^ (s.re / 2 - 1) * (21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t)) :=
      mul_le_mul_of_nonneg_left (norm_f_modif_le_of_lt_one ht hlt) (Real.rpow_nonneg ht.le _)
    refine hstep.trans ?_
    have hcomb : t ^ (s.re / 2 - 1) * (21 / 10 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t))
        = 21 / 10 * (t ^ (s.re / 2 - 3 / 2) * rexp (-π / t)) := by
      rw [show s.re / 2 - 3 / 2 = (s.re / 2 - 1) + (-(1 : ℝ) / 2) by ring, Real.rpow_add ht]
      ring
    rw [hcomb]
    have hexp : t ^ (s.re / 2 - 3 / 2) ≤ t ^ (-3 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht hlt.le (by linarith)
    have hnn : (0 : ℝ) ≤ rexp (-π / t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (-3 / 2 : ℝ), Real.rpow_pos_of_pos ht (s.re / 2 - 3 / 2)]
  · have hm : maj (1 : ℝ) = 21 / 10 * ((1 : ℝ) ^ (-3 / 2 : ℝ) * rexp (-π / 1)) := if_pos le_rfl
    rw [hm, f_modif_one]
    simp only [norm_zero, mul_zero]
    positivity
  · have hmaj : maj t = 21 / 10 * (t ^ (-(1 : ℝ) / 2) * rexp (-π * t)) := by
      simp [maj, not_le.2 hgt]
    rw [hmaj]
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤ t ^ (s.re / 2 - 1) * (21 / 10 * rexp (-π * t)) :=
      mul_le_mul_of_nonneg_left (norm_f_modif_le_of_one_lt hgt) (Real.rpow_nonneg ht.le _)
    refine hstep.trans ?_
    have hexp : t ^ (s.re / 2 - 1) ≤ t ^ (-(1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hgt.le (by linarith)
    have hnn : (0 : ℝ) ≤ rexp (-π * t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (-(1 : ℝ) / 2), Real.rpow_pos_of_pos ht (s.re / 2 - 1)]

/-- **Sharpened bound on the entire part of the completed zeta function.**
In the critical strip, `‖Λ₀ s‖ ≤ 0.0268`. -/
theorem norm_completedRiemannZeta₀_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ‖completedRiemannZeta₀ s‖ ≤ 0.0268 := by
  have hdef : completedRiemannZeta₀ s = mellin P.f_modif (s / 2) / 2 := rfl
  rw [hdef, norm_div, Complex.norm_ofNat]
  have hb : ‖mellin P.f_modif (s / 2)‖ ≤ ∫ t in Ioi (0 : ℝ), maj t := by
    rw [mellin]
    refine norm_integral_le_of_norm_le integrableOn_maj ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    exact norm_integrand_le h0 h1 ht
  have := hb.trans integral_maj_le
  linarith

lemma norm_mul_one_sub_le {s : ℂ} (him : |s.im| ≤ 6) (h0 : 0 < s.re) (h1 : s.re < 1) :
    ‖s‖ * ‖1 - s‖ ≤ 36.5 := by
  have hs : ‖s‖ ^ 2 ≤ s.re ^ 2 + 36 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [abs_le.1 him, sq_abs s.im]
  have hs' : ‖1 - s‖ ^ 2 ≤ (1 - s.re) ^ 2 + 36 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    nlinarith [abs_le.1 him, sq_abs s.im]
  have hprod : (‖s‖ * ‖1 - s‖) ^ 2 ≤ 1332 := by
    have hb1 : s.re ^ 2 + 36 ≤ 37 := by nlinarith
    have hb2 : (1 - s.re) ^ 2 + 36 ≤ 37 := by nlinarith
    have h1' : ‖s‖ ^ 2 * ‖1 - s‖ ^ 2 ≤ (s.re ^ 2 + 36) * ((1 - s.re) ^ 2 + 36) := by
      have := sq_nonneg ‖s‖
      have := sq_nonneg ‖1 - s‖
      nlinarith [norm_nonneg s, norm_nonneg (1 - s)]
    have h2' : (s.re ^ 2 + 36) * ((1 - s.re) ^ 2 + 36) ≤ 1332 := by
      nlinarith [sq_nonneg s.re, sq_nonneg (1 - s.re), sq_nonneg (s.re * (1 - s.re)),
        mul_nonneg (sq_nonneg s.re) (sq_nonneg (1 - s.re))]
    calc (‖s‖ * ‖1 - s‖) ^ 2 = ‖s‖ ^ 2 * ‖1 - s‖ ^ 2 := by ring
      _ ≤ (s.re ^ 2 + 36) * ((1 - s.re) ^ 2 + 36) := h1'
      _ ≤ 1332 := h2'
  nlinarith [mul_nonneg (norm_nonneg s) (norm_nonneg (1 - s))]

/-- **The completed zeta function has no zeros of height at most 6 in the critical strip.** -/
theorem completedRiemannZeta_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : |s.im| ≤ 6) : completedRiemannZeta s ≠ 0 := by
  intro hz
  have hs0 : s ≠ 0 := fun h => by simp [h] at h0
  have hs1 : s ≠ 1 := by rintro rfl; simp at h1
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  have key : completedRiemannZeta₀ s = 1 / (s * (1 - s)) := by
    have h := completedRiemannZeta_eq s
    rw [hz] at h
    have hsum : completedRiemannZeta₀ s = 1 / s + 1 / (1 - s) := by linear_combination -h
    rw [hsum]
    field_simp
    ring
  have hnorm : ‖completedRiemannZeta₀ s‖ = 1 / (‖s‖ * ‖1 - s‖) := by
    rw [key, norm_div, norm_one, norm_mul]
  have hb := norm_completedRiemannZeta₀_le h0 h1
  rw [hnorm] at hb
  have hpos : 0 < ‖s‖ * ‖1 - s‖ := mul_pos (norm_pos_iff.2 hs0) (norm_pos_iff.2 h1s)
  have h36 := norm_mul_one_sub_le him h0 h1
  rw [div_le_iff₀ hpos] at hb
  nlinarith

/-- **An explicit zero-free rectangle of height 6 for the Riemann zeta function.**
`ζ` has no zero `s` with `0 < Re s < 1` and `|Im s| ≤ 6`. -/
theorem riemannZeta_ne_zero_of_abs_im_le_six {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : |s.im| ≤ 6) : riemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at h0
  rw [riemannZeta_def_of_ne_zero hs0]
  intro hz
  rcases div_eq_zero_iff.mp hz with h | h
  · exact completedRiemannZeta_ne_zero h0 h1 him h
  · exact Complex.Gammaℝ_ne_zero_of_re_pos h0 h

/-- **Reduction of the half-plane form of the Riemann hypothesis to height `> 6`.** -/
theorem zeta_ne_zero_of_half_lt_re_of_high_zeros_free
    (H : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → 6 < |s.im| → riemannZeta s ≠ 0)
    (s : ℂ) (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  rcases le_or_gt 1 s.re with h | h
  · exact riemannZeta_ne_zero_of_one_le_re h
  · rcases le_or_gt |s.im| 6 with h6 | h6
    · exact riemannZeta_ne_zero_of_abs_im_le_six (by linarith) h h6
    · exact H s hs h h6

end ZetaSix

/-- **An explicit zero-free rectangle of height 6 for the Riemann zeta function.** -/
theorem solution (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (him : |s.im| ≤ 6) :
    riemannZeta s ≠ 0 :=
  ZetaSix.riemannZeta_ne_zero_of_abs_im_le_six h0 h1 him
