-- Prove2me | solution 1 for lean_workbook_plus_10876
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:41:47.613922+00:00
-- url     : https://prove2.me/submissions/f185999c-3b6b-42fa-b7c4-efd2fc1a445f

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Set

noncomputable def radicalMobiusIntegrand (x : ℝ) : ℝ :=
  (x - 2) / ((7 * x ^ 2 - 36 * x + 48) * Real.sqrt (x ^ 2 - 2 * x - 1))

noncomputable def radicalMobiusChartPrimitive (x : ℝ) : ℝ :=
  Real.arctan ((3 * Real.sqrt (x ^ 2 - 2 * x - 1) / (3 - x)) / Real.sqrt 33) /
    Real.sqrt 33

noncomputable def radicalMobiusRegularPrimitive (x : ℝ) : ℝ :=
  -(Real.arctan ((11 * (3 - x) / Real.sqrt (x ^ 2 - 2 * x - 1)) / Real.sqrt 33) /
    Real.sqrt 33)

theorem radical_mobius_quadratic_pos (x : ℝ) : 0 < 7 * x ^ 2 - 36 * x + 48 := by
  nlinarith [sq_nonneg (7 * x - 18)]

theorem radical_mobius_domain (x : ℝ) :
    0 < x ^ 2 - 2 * x - 1 ↔ x < 1 - Real.sqrt 2 ∨ 1 + Real.sqrt 2 < x := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  constructor
  · intro hx
    by_contra hn
    push_neg at hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hn.1) (sub_nonneg.mpr hn.2)]
  · rintro (h | h)
    · nlinarith [mul_pos (sub_pos.mpr h) (show 0 < 1 + Real.sqrt 2 - x by linarith)]
    · nlinarith [mul_pos (sub_pos.mpr h) (show 0 < x - (1 - Real.sqrt 2) by linarith)]

theorem scaled_arctan_hasDerivAt {g : ℝ → ℝ} {d x : ℝ}
    (hg : HasDerivAt g d x) (c : ℝ) (hc : 0 < c) :
    HasDerivAt (fun y => Real.arctan (g y / c) / c) (d / ((g x) ^ 2 + c ^ 2)) x := by
  have hd := ((hg.div_const c).arctan).div_const c
  convert hd using 1
  have hn : (g x) ^ 2 + c ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hq : 1 + (g x / c) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  <;> ring

theorem radical_mobius_sqrt_hasDerivAt (x : ℝ) (hx : 0 < x ^ 2 - 2 * x - 1) :
    HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 - 2 * y - 1))
      ((x - 1) / Real.sqrt (x ^ 2 - 2 * x - 1)) x := by
  have hp : HasDerivAt (fun y : ℝ => y ^ 2 - 2 * y - 1)
      ((1 * x + x * 1) - 2 * 1) x := by
    simpa only [pow_two, id_eq] using
      ((((hasDerivAt_id x).mul (hasDerivAt_id x)).sub
        ((hasDerivAt_id x).const_mul 2)).sub_const 1)
  have hd := hp.sqrt hx.ne'
  convert hd using 1 <;> ring

theorem radical_mobius_chart_algebra (x s : ℝ) (hs : s ^ 2 = x ^ 2 - 2 * x - 1)
    (hs0 : s ≠ 0) (hx3 : 3 - x ≠ 0) :
    ((3 * ((x - 1) / s) * (3 - x) - 3 * s * (-1)) / (3 - x) ^ 2) /
      ((3 * s / (3 - x)) ^ 2 + 33) = (x - 2) / ((7 * x ^ 2 - 36 * x + 48) * s) := by
  have hq := ne_of_gt (radical_mobius_quadratic_pos x)
  have hn : (3 * s / (3 - x)) ^ 2 + 33 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  have hq' : x * (x * 7 - 36) + 48 ≠ 0 := by convert hq using 1 <;> ring
  apply (eq_div_iff hq').mpr
  rw [hs]
  ring

theorem radical_mobius_regular_algebra (x s : ℝ) (hs : s ^ 2 = x ^ 2 - 2 * x - 1)
    (hs0 : s ≠ 0) :
    -(((11 * (-1) * s - 11 * (3 - x) * ((x - 1) / s)) / s ^ 2) /
      ((11 * (3 - x) / s) ^ 2 + 33)) = (x - 2) / ((7 * x ^ 2 - 36 * x + 48) * s) := by
  have hq := ne_of_gt (radical_mobius_quadratic_pos x)
  have hn : (11 * (3 - x) / s) ^ 2 + 33 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  have hq' : x * (x * 7 - 36) + 48 ≠ 0 := by convert hq using 1 <;> ring
  apply (eq_div_iff hq').mpr
  rw [hs]
  ring

theorem radical_mobius_chart_hasDerivAt (x : ℝ) (hx : 0 < x ^ 2 - 2 * x - 1)
    (hx3 : x ≠ 3) : HasDerivAt radicalMobiusChartPrimitive (radicalMobiusIntegrand x) x := by
  have hs := radical_mobius_sqrt_hasDerivAt x hx
  have hz : 3 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx3)
  have hd := scaled_arctan_hasDerivAt
    ((hs.const_mul 3).div ((hasDerivAt_id x).const_sub 3) hz) (Real.sqrt 33)
      (Real.sqrt_pos.2 (by norm_num))
  simp only [id_eq, Real.sq_sqrt (show (0 : ℝ) ≤ 33 by norm_num)] at hd
  convert hd using 1
  exact (radical_mobius_chart_algebra x _ (Real.sq_sqrt hx.le)
    (Real.sqrt_pos.2 hx).ne' hz).symm

theorem radical_mobius_regular_hasDerivAt (x : ℝ) (hx : 0 < x ^ 2 - 2 * x - 1) :
    HasDerivAt radicalMobiusRegularPrimitive (radicalMobiusIntegrand x) x := by
  have hs := radical_mobius_sqrt_hasDerivAt x hx
  have hd := (scaled_arctan_hasDerivAt
    ((((hasDerivAt_id x).const_sub 3).const_mul 11).div hs (Real.sqrt_pos.2 hx).ne')
      (Real.sqrt 33) (Real.sqrt_pos.2 (by norm_num))).neg
  simp only [id_eq, Real.sq_sqrt (show (0 : ℝ) ≤ 33 by norm_num)] at hd
  convert hd using 1
  exact (radical_mobius_regular_algebra x _ (Real.sq_sqrt hx.le)
    (Real.sqrt_pos.2 hx).ne').symm

theorem radical_mobius_intervalIntegrable (a b : ℝ)
    (h : ∀ x ∈ uIcc a b, 0 < x ^ 2 - 2 * x - 1) :
    IntervalIntegrable radicalMobiusIntegrand volume a b := by
  have hc : ContinuousOn radicalMobiusIntegrand (uIcc a b) := by
    apply (continuous_id.sub continuous_const).continuousOn.div
      ((((continuous_const.mul (continuous_id.pow 2)).sub
        (continuous_const.mul continuous_id)).add continuous_const).mul
        (Real.continuous_sqrt.comp (((continuous_id.pow 2).sub
          (continuous_const.mul continuous_id)).sub continuous_const))).continuousOn
    intro x hx
    exact mul_ne_zero (radical_mobius_quadratic_pos x).ne' (Real.sqrt_pos.2 (h x hx)).ne'
  exact hc.intervalIntegrable

theorem radical_mobius_integral (a b : ℝ)
    (h : ∀ x ∈ uIcc a b, 0 < x ^ 2 - 2 * x - 1) :
    (∫ x in a..b, radicalMobiusIntegrand x) =
      radicalMobiusRegularPrimitive b - radicalMobiusRegularPrimitive a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => radical_mobius_regular_hasDerivAt x (h x hx))
    (radical_mobius_intervalIntegrable a b h)

theorem radical_mobius_chart_integral (a b : ℝ)
    (h : ∀ x ∈ uIcc a b, 0 < x ^ 2 - 2 * x - 1 ∧ x ≠ 3) :
    (∫ x in a..b, radicalMobiusIntegrand x) =
      radicalMobiusChartPrimitive b - radicalMobiusChartPrimitive a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => radical_mobius_chart_hasDerivAt x (h x hx).1 (h x hx).2)
    (radical_mobius_intervalIntegrable a b (fun x hx => (h x hx).1))

theorem radical_mobius_substitution (t : ℝ) (ht : t + 1 ≠ 0) :
    let x := (3 * t + 2) / (t + 1)
    (x - 2) / (3 - x) = t ∧
      x ^ 2 - 2 * x - 1 = (2 * t ^ 2 - 1) / (t + 1) ^ 2 ∧
      7 * x ^ 2 - 36 * x + 48 = (3 * t ^ 2 + 4) / (t + 1) ^ 2 := by
  dsimp
  have hz : 3 - (3 * t + 2) / (t + 1) ≠ 0 := by
    intro h
    have he : 3 * (t + 1) = 3 * t + 2 := (eq_div_iff ht).mp (sub_eq_zero.mp h)
    linarith
  constructor
  · field_simp
    <;> ring
  constructor <;> field_simp <;> ring

theorem radical_mobius_inverse_substitution_hasDerivAt (t : ℝ) (ht : t + 1 ≠ 0) :
    HasDerivAt (fun y : ℝ => (3 * y + 2) / (y + 1)) (1 / (t + 1) ^ 2) t := by
  have hd := (((hasDerivAt_id t).const_mul 3).add_const 2).div
    ((hasDerivAt_id t).add_const 1) ht
  simp only [id_eq] at hd
  convert hd using 1 <;> ring

theorem solution (x t : ℝ) (f : ℝ → ℝ)
    (hf : f x = (x - 2) / (7 * x ^ 2 - 36 * x + 48) * Real.sqrt (x ^ 2 - 2 * x - 1))
    (h : t = (x - 2) / (3 - x)) : ∃ k : ℝ, ∃ g : ℝ → ℝ, f x = k * g t := by
  exact ⟨f x, fun _ => 1, (mul_one _).symm⟩

#print axioms radicalMobiusIntegrand
#print axioms radicalMobiusChartPrimitive
#print axioms radicalMobiusRegularPrimitive
#print axioms radical_mobius_quadratic_pos
#print axioms radical_mobius_domain
#print axioms scaled_arctan_hasDerivAt
#print axioms radical_mobius_sqrt_hasDerivAt
#print axioms radical_mobius_chart_algebra
#print axioms radical_mobius_regular_algebra
#print axioms radical_mobius_chart_hasDerivAt
#print axioms radical_mobius_regular_hasDerivAt
#print axioms radical_mobius_intervalIntegrable
#print axioms radical_mobius_integral
#print axioms radical_mobius_chart_integral
#print axioms radical_mobius_substitution
#print axioms radical_mobius_inverse_substitution_hasDerivAt
#print axioms solution
