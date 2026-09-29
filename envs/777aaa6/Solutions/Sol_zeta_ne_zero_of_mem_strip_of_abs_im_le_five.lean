-- Prove2me | solution 1 for zeta_ne_zero_of_mem_strip_of_abs_im_le_five
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T13:24:04.677005+00:00
-- url     : https://prove2.me/submissions/133ec6c3-5e74-4d40-be18-ff97897ac976

/-
An explicit zero-free rectangle for the Riemann zeta function:
`ζ s ≠ 0` whenever `0 < Re s < 1` and `|Im s| ≤ 5`.

Self-contained solution file: it re-proves, from Mathlib only, the bounds on the Jacobi theta
kernel that Mathlib's completed zeta function is built from.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Complex MeasureTheory Set HurwitzZeta Real
open scoped Real

namespace ZetaFive

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

/-! ### The integral over `(0,1)` via the change of variables `t ↦ 1/t` -/

/-- The exponential tail, cut off below `1`; used as the target of the substitution `t ↦ 1/t`. -/
private noncomputable def gInd : ℝ → ℝ := Set.indicator (Ioi 1) fun y => rexp (-π * y)

private lemma gInd_integrableOn : IntegrableOn gInd (Ioi (0 : ℝ)) := by
  have h : IntegrableOn (fun y : ℝ => rexp (-π * y)) (Ioi (1 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 1 Real.pi_pos).congr_fun (fun t _ => by ring_nf) measurableSet_Ioi
  rw [gInd]
  exact (h.integrable_indicator measurableSet_Ioi).integrableOn

private lemma integral_gInd : (∫ y in Ioi (0 : ℝ), gInd y) = rexp (-π) / π := by
  have h : (∫ y in Ioi (0 : ℝ), gInd y) = ∫ y in Ioi (1 : ℝ), rexp (-π * y) := by
    rw [gInd, MeasureTheory.integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi]
    norm_num
  rw [h]
  have h2 := MeasureTheory.integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) 1 Real.pi_pos
  simp only [smul_eq_mul, mul_one] at h2
  rw [show (fun t : ℝ => Real.exp (-π * t)) = (fun t : ℝ => Real.exp (-(π * t))) by
    ext t; ring_nf]
  rw [h2, integral_exp_neg_Ioi]
  ring

private lemma cov_ptwise (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))
      = (Ioo (0 : ℝ) 1).indicator (fun x => x ^ (-2 : ℝ) * rexp (-π / x)) x := by
  have hx0 : 0 < x := hx
  have hinv : x ^ (-1 : ℝ) = x⁻¹ := by rw [Real.rpow_neg_one]
  rcases lt_or_ge x 1 with h | h
  · have h1 : (1 : ℝ) < x⁻¹ := by rw [lt_inv_comm₀ (by norm_num) hx0]; simpa using h
    rw [Set.indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from ⟨hx0, h⟩), gInd, hinv,
      Set.indicator_of_mem (mem_Ioi.mpr h1)]
    have hd : -π * x⁻¹ = -π / x := by field_simp
    rw [hd]
    norm_num
  · have h1 : x⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; exact h
    rw [Set.indicator_of_notMem (by simp; intro _; exact h), gInd, hinv,
      Set.indicator_of_notMem (by simp [not_lt.2 h1])]
    simp

/-- The kernel `x ^ (-2) e ^ (-π/x)` is integrable on `(0,1]`. -/
lemma integrableOn_inner :
    IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ) * rexp (-π / x)) (Ioc (0 : ℝ) 1) := by
  have h1 : IntegrableOn
      (fun x : ℝ => (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • gInd (x ^ (-1 : ℝ))) (Ioi 0) :=
    (MeasureTheory.integrableOn_Ioi_comp_rpow_iff gInd (by norm_num : (-1 : ℝ) ≠ 0)).mpr
      gInd_integrableOn
  have h2 : IntegrableOn
      ((Ioo (0 : ℝ) 1).indicator fun x => x ^ (-2 : ℝ) * rexp (-π / x)) (Ioi 0) :=
    h1.congr_fun cov_ptwise measurableSet_Ioi
  have h3 := (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mp h2
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioo,
    show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at h3
  rw [IntegrableOn, ← MeasureTheory.Measure.restrict_congr_set
    (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact h3

/-- **The exact value of the low part of the majorant integral.**  The substitution `x ↦ 1/x`
turns `∫₀¹ x^{-2} e^{-π/x} dx` into `∫₁^∞ e^{-π u} du = e^{-π}/π`. -/
lemma integral_inner : (∫ x in Ioc (0 : ℝ) 1, x ^ (-2 : ℝ) * rexp (-π / x)) = rexp (-π) / π := by
  have hcov := MeasureTheory.integral_comp_rpow_Ioi gInd (by norm_num : (-1 : ℝ) ≠ 0)
  rw [integral_gInd] at hcov
  rw [setIntegral_congr_fun measurableSet_Ioi cov_ptwise] at hcov
  rw [MeasureTheory.integral_indicator measurableSet_Ioo, Measure.restrict_restrict
    measurableSet_Ioo, show Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo (0 : ℝ) 1 by
      ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]; tauto] at hcov
  rw [← MeasureTheory.Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  exact hcov

/-! ### The majorant -/

/-- Integrable majorant for the Mellin integrand of `Λ₀` on `(0, ∞)`, valid uniformly for
`0 < Re s < 1`. -/
noncomputable def maj (t : ℝ) : ℝ :=
  if t ≤ 1 then 5 / 2 * (t ^ (-2 : ℝ) * rexp (-π / t)) else 5 / 2 * rexp (-π * t)

lemma integrableOn_maj_Ioc : IntegrableOn maj (Ioc (0 : ℝ) 1) := by
  have h : IntegrableOn (fun x : ℝ => 5 / 2 * (x ^ (-2 : ℝ) * rexp (-π / x))) (Ioc (0 : ℝ) 1) :=
    integrableOn_inner.const_mul (5 / 2)
  refine h.congr_fun ?_ measurableSet_Ioc
  intro t ht
  simp [maj, ht.2]

lemma integrableOn_maj_Ioi : IntegrableOn maj (Ioi (1 : ℝ)) := by
  have h : IntegrableOn (fun t : ℝ => 5 / 2 * rexp (-π * t)) (Ioi (1 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 1 Real.pi_pos).const_mul _
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  simp [maj, not_le.2 (mem_Ioi.mp ht)]

lemma integrableOn_maj : IntegrableOn maj (Ioi 0) := by
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  exact integrableOn_maj_Ioc.union integrableOn_maj_Ioi

lemma integral_maj_le : ∫ t in Ioi (0 : ℝ), maj t ≤ 1 / 14 := by
  have hsplit : ∫ t in Ioi (0 : ℝ), maj t
      = (∫ t in Ioc (0 : ℝ) 1, maj t) + ∫ t in Ioi (1 : ℝ), maj t := by
    rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
    exact setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi
      integrableOn_maj_Ioc integrableOn_maj_Ioi
  have h1 : ∫ t in Ioc (0 : ℝ) 1, maj t = 5 / 2 * (rexp (-π) / π) := by
    rw [setIntegral_congr_fun measurableSet_Ioc
      (g := fun t : ℝ => 5 / 2 * (t ^ (-2 : ℝ) * rexp (-π / t))) (fun t ht => by simp [maj, ht.2]),
      integral_const_mul, integral_inner]
  have h2 : ∫ t in Ioi (1 : ℝ), maj t = 5 / 2 * (rexp (-π) / π) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ => 5 / 2 * rexp (-π * t))
      (fun t ht => by simp [maj, not_le.2 (mem_Ioi.mp ht)]), integral_const_mul]
    congr 1
    have h := MeasureTheory.integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) 1 Real.pi_pos
    simp only [smul_eq_mul, mul_one] at h
    rw [show (fun t : ℝ => Real.exp (-π * t)) = (fun t : ℝ => Real.exp (-(π * t))) by
      ext t; ring_nf]
    rw [h, integral_exp_neg_Ioi]
    ring
  rw [hsplit, h1, h2]
  have hpi : (3.14 : ℝ) < π := Real.pi_gt_d2
  have hpos : (0 : ℝ) < rexp (-π) := Real.exp_pos _
  have hb : rexp (-π) / π ≤ (1 / 23) / 3.14 := by
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < π) (by norm_num : (0 : ℝ) < 3.14)]
    nlinarith [exp_neg_pi_le_23, Real.exp_pos (-π)]
  linarith

/-! ### The improved bound on `Λ₀` -/

/-- The pointwise bound for the Mellin integrand of `Λ₀` in the critical strip. -/
lemma norm_integrand_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s / 2 - 1) • P.f_modif t‖ ≤ maj t := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    show (s / 2 - 1).re = s.re / 2 - 1 by simp]
  rcases lt_trichotomy t 1 with hlt | rfl | hgt
  · have hmaj : maj t = 5 / 2 * (t ^ (-2 : ℝ) * rexp (-π / t)) := by simp [maj, hlt.le]
    rw [hmaj]
    have hstep : t ^ (s.re / 2 - 1) * ‖P.f_modif t‖
        ≤ t ^ (s.re / 2 - 1) * (5 / 2 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t)) :=
      mul_le_mul_of_nonneg_left (norm_f_modif_le_of_lt_one ht hlt) (Real.rpow_nonneg ht.le _)
    refine hstep.trans ?_
    have hcomb : t ^ (s.re / 2 - 1) * (5 / 2 * t ^ (-(1 : ℝ) / 2) * rexp (-π / t))
        = 5 / 2 * (t ^ (s.re / 2 - 3 / 2) * rexp (-π / t)) := by
      rw [show s.re / 2 - 3 / 2 = (s.re / 2 - 1) + (-(1 : ℝ) / 2) by ring, Real.rpow_add ht]
      ring
    rw [hcomb]
    have hexp : t ^ (s.re / 2 - 3 / 2) ≤ t ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht hlt.le (by linarith)
    have hnn : (0 : ℝ) ≤ rexp (-π / t) := (Real.exp_pos _).le
    nlinarith [Real.rpow_pos_of_pos ht (-2 : ℝ), Real.rpow_pos_of_pos ht (s.re / 2 - 3 / 2)]
  · have hm : maj (1 : ℝ) = 5 / 2 * ((1 : ℝ) ^ (-2 : ℝ) * rexp (-π / 1)) := if_pos le_rfl
    rw [hm, f_modif_one]
    simp only [norm_zero, mul_zero]
    positivity
  · have hmaj : maj t = 5 / 2 * rexp (-π * t) := by simp [maj, not_le.2 hgt]
    rw [hmaj]
    have h1' : t ^ (s.re / 2 - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hgt.le (by linarith)
    calc t ^ (s.re / 2 - 1) * ‖P.f_modif t‖ ≤ 1 * ‖P.f_modif t‖ := by gcongr
      _ = ‖P.f_modif t‖ := one_mul _
      _ ≤ 5 / 2 * rexp (-π * t) := norm_f_modif_le_of_one_lt hgt

/-- **Improved explicit bound on the entire part of the completed zeta function.**
In the critical strip, `‖Λ₀ s‖ ≤ 1/28`. -/
theorem norm_completedRiemannZeta₀_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ‖completedRiemannZeta₀ s‖ ≤ 1 / 28 := by
  have hdef : completedRiemannZeta₀ s = mellin P.f_modif (s / 2) / 2 := rfl
  rw [hdef, norm_div, Complex.norm_ofNat]
  have hb : ‖mellin P.f_modif (s / 2)‖ ≤ ∫ t in Ioi (0 : ℝ), maj t := by
    rw [mellin]
    refine norm_integral_le_of_norm_le integrableOn_maj ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    exact norm_integrand_le h0 h1 ht
  have := hb.trans integral_maj_le
  linarith

/-! ### The zero-free rectangle of height 5 -/

lemma norm_mul_one_sub_le {s : ℂ} (him : |s.im| ≤ 5) (h0 : 0 < s.re) (h1 : s.re < 1) :
    ‖s‖ * ‖1 - s‖ ≤ 26 := by
  have hs : ‖s‖ ^ 2 ≤ 26 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [abs_le.1 him, sq_abs s.im]
  have hs' : ‖1 - s‖ ^ 2 ≤ 26 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    nlinarith [abs_le.1 him, sq_abs s.im]
  nlinarith [norm_nonneg s, norm_nonneg (1 - s)]

/-- **The completed zeta function has no zeros of height at most 5 in the critical strip.** -/
theorem completedRiemannZeta_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : |s.im| ≤ 5) : completedRiemannZeta s ≠ 0 := by
  intro hz
  have hs0 : s ≠ 0 := fun h => by simp [h] at h0
  have hs1 : s ≠ 1 := by rintro rfl; simp at h1
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  have key : completedRiemannZeta₀ s = 1 / (s * (1 - s)) := by
    have h := completedRiemannZeta_eq s
    rw [hz] at h
    have : completedRiemannZeta₀ s = 1 / s + 1 / (1 - s) := by linear_combination -h
    rw [this]
    field_simp
    ring
  have hnorm : ‖completedRiemannZeta₀ s‖ = 1 / (‖s‖ * ‖1 - s‖) := by
    rw [key, norm_div, norm_one, norm_mul]
  have hb := norm_completedRiemannZeta₀_le h0 h1
  rw [hnorm] at hb
  have hpos : 0 < ‖s‖ * ‖1 - s‖ := mul_pos (norm_pos_iff.2 hs0) (norm_pos_iff.2 h1s)
  have h26 := norm_mul_one_sub_le him h0 h1
  rw [div_le_iff₀ hpos] at hb
  linarith

/-- **An explicit zero-free rectangle of height 5 for the Riemann zeta function.**
`ζ` has no zero `s` with `0 < Re s < 1` and `|Im s| ≤ 5`. -/
theorem riemannZeta_ne_zero_of_abs_im_le_five {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : |s.im| ≤ 5) : riemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at h0
  rw [riemannZeta_def_of_ne_zero hs0]
  intro hz
  rcases div_eq_zero_iff.mp hz with h | h
  · exact completedRiemannZeta_ne_zero h0 h1 him h
  · exact Complex.Gammaℝ_ne_zero_of_re_pos h0 h

/-- **Reduction of the half-plane form of the Riemann hypothesis to height `> 5`.**
The statement "`ζ` has no zeros with `Re s > 1/2`" — which is equivalent to the Riemann
hypothesis — follows from the a priori weaker statement about zeros of height `|Im s| > 5`. -/
theorem zeta_ne_zero_of_half_lt_re_of_high_zeros_free
    (H : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → 5 < |s.im| → riemannZeta s ≠ 0)
    (s : ℂ) (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  rcases le_or_gt 1 s.re with h | h
  · exact riemannZeta_ne_zero_of_one_le_re h
  · rcases le_or_gt |s.im| 5 with h5 | h5
    · exact riemannZeta_ne_zero_of_abs_im_le_five (by linarith) h h5
    · exact H s hs h h5

end ZetaFive

/-- **An explicit zero-free rectangle of height 5 for the Riemann zeta function.** -/
theorem solution (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) (him : |s.im| ≤ 5) :
    riemannZeta s ≠ 0 :=
  ZetaFive.riemannZeta_ne_zero_of_abs_im_le_five h0 h1 him
