-- Prove2me | solution 1 for Goldbach.density_kernel_taylor_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T03:31:00.45774+00:00
-- url     : https://prove2.me/submissions/ec00086c-62a2-40fe-a65e-5063516f059c

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp

open MeasureTheory
open scoped BigOperators
set_option autoImplicit false

private lemma expanded_moment (n : ℕ) :
    (∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*u^n) =
    (16/15:ℝ)*2^(n+1)/(n+1) - (4/3:ℝ)*2^(n+3)/(n+3) +
    (2/3:ℝ)*2^(n+4)/(n+4) - (1/30:ℝ)*2^(n+6)/(n+6) := by
  have hp (k : ℕ) : IntervalIntegrable (fun u : ℝ => u^k) volume 0 2 :=
    (continuous_id.pow k).intervalIntegrable 0 2
  have he : (fun u : ℝ => ((2-u)^3*(4+6*u+u^2)/30)*u^n) =
      (fun u : ℝ => (16/15)*u^n-(4/3)*u^(n+2)+(2/3)*u^(n+3)-(1/30)*u^(n+5)) := by
    funext u
    simp only [pow_add]
    ring
  rw [he]
  have h1 := (hp n).const_mul (16/15:ℝ)
  have h2 := (hp (n+2)).const_mul (4/3:ℝ)
  have h3 := (hp (n+3)).const_mul (2/3:ℝ)
  have h4 := (hp (n+5)).const_mul (1/30:ℝ)
  rw [intervalIntegral.integral_sub ((h1.sub h2).add h3) h4,
    intervalIntegral.integral_add (h1.sub h2) h3,
    intervalIntegral.integral_sub h1 h2]
  simp only [intervalIntegral.integral_const_mul,integral_pow,
    zero_pow (Nat.add_pos_right _ (by omega))]
  push_cast
  ring

private theorem moment_formula (n : ℕ) :
    (∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*u^n) =
      4*(2:ℝ)^(n+4)/(5*((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)*((n:ℝ)+4)) +
      6*(2:ℝ)^(n+5)/(5*((n:ℝ)+2)*((n:ℝ)+3)*((n:ℝ)+4)*((n:ℝ)+5)) +
      (2:ℝ)^(n+6)/(5*((n:ℝ)+3)*((n:ℝ)+4)*((n:ℝ)+5)*((n:ℝ)+6)) := by
  rw [expanded_moment]
  have h1 : (n:ℝ)+1 ≠ 0 := by positivity
  have h2 : (n:ℝ)+2 ≠ 0 := by positivity
  have h3 : (n:ℝ)+3 ≠ 0 := by positivity
  have h4 : (n:ℝ)+4 ≠ 0 := by positivity
  have h5 : (n:ℝ)+5 ≠ 0 := by positivity
  have h6 : (n:ℝ)+6 ≠ 0 := by positivity
  simp only [pow_add]
  norm_num
  field_simp
  ring



private lemma real_taylor_bound (w : ℝ) (n : ℕ)
    (h : |w|/(n+1) ≤ (1/2:ℝ)) :
    |Real.exp w - ∑ k ∈ Finset.range n, w^k/(k.factorial:ℝ)| ≤
      |w|^n/(n.factorial:ℝ)*2 := by
  have hC : ‖(w:ℂ)‖/(n.succ:ℝ) ≤ (1/2:ℝ) := by simpa using h
  have hb := Complex.exp_bound' hC
  have he : ((Real.exp w - ∑ k ∈ Finset.range n, w^k/(k.factorial:ℝ):ℝ):ℂ) =
      Complex.exp (w:ℂ) - ∑ k ∈ Finset.range n, (w:ℂ)^k/(k.factorial:ℂ) := by
    push_cast
    rfl
  rw [← he] at hb
  simpa only [Complex.norm_real,Real.norm_eq_abs] using hb

private noncomputable def kernel (u : ℝ) : ℝ := (2-u)^3*(4+6*u+u^2)/30

private lemma kernel_nonnegative (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 2) :
    0 ≤ kernel u := by
  apply div_nonneg
  · apply mul_nonneg
    · exact pow_nonneg (sub_nonneg.mpr hu.2) _
    · nlinarith [sq_nonneg u,hu.1]
  · norm_num

private lemma kernel_mass : (∫ u in (0:ℝ)..2, kernel u) = (8/9:ℝ) := by
  have h := moment_formula 0
  norm_num [kernel] at h ⊢
  exact h

private lemma polynomial_integral (n : ℕ) (z : ℝ) :
    (∫ u in (0:ℝ)..2, kernel u*(∑ k ∈ Finset.range n, (-z*u)^k/(k.factorial:ℝ))) =
      ∑ k ∈ Finset.range n, ((-z)^k/(k.factorial:ℝ))*
        (∫ u in (0:ℝ)..2, kernel u*u^k) := by
  have hfun : (fun u : ℝ => kernel u*(∑ k ∈ Finset.range n, (-z*u)^k/(k.factorial:ℝ))) =
      (fun u : ℝ => ∑ k ∈ Finset.range n, ((-z)^k/(k.factorial:ℝ))*(kernel u*u^k)) := by
    funext u
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow]
    ring
  rw [hfun,intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul]
  · intro k _
    exact (by unfold kernel; fun_prop : Continuous (fun u : ℝ => ((-z)^k/(k.factorial:ℝ))*(kernel u*u^k))).intervalIntegrable 0 2

theorem solution (n : ℕ) (z : ℝ) (hz : 4*|z| ≤ (n:ℝ)+1) :
    |(∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*Real.exp (-z*u)) -
      ∑ k ∈ Finset.range n, ((-z)^k/(k.factorial:ℝ))*
        (4*(2:ℝ)^(k+4)/(5*((k:ℝ)+1)*((k:ℝ)+2)*((k:ℝ)+3)*((k:ℝ)+4)) +
         6*(2:ℝ)^(k+5)/(5*((k:ℝ)+2)*((k:ℝ)+3)*((k:ℝ)+4)*((k:ℝ)+5)) +
         (2:ℝ)^(k+6)/(5*((k:ℝ)+3)*((k:ℝ)+4)*((k:ℝ)+5)*((k:ℝ)+6)))| ≤
      (16/9:ℝ)*(2*|z|)^n/(n.factorial:ℝ) := by
  let P : ℝ → ℝ := fun u => ∑ k ∈ Finset.range n, (-z*u)^k/(k.factorial:ℝ)
  let R : ℝ := (2*|z|)^n/(n.factorial:ℝ)*2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hp : Continuous P := by dsimp [P]; fun_prop
  have hg : Continuous kernel := by unfold kernel; fun_prop
  have he : Continuous (fun u : ℝ => kernel u*Real.exp (-z*u)) := by fun_prop
  have hpoly : Continuous (fun u : ℝ => kernel u*P u) := hg.mul hp
  have hdiff : Continuous (fun u : ℝ => kernel u*(Real.exp (-z*u)-P u)) := by fun_prop
  have hpoint : ∀ u ∈ Set.Icc (0:ℝ) 2,
      |kernel u*(Real.exp (-z*u)-P u)| ≤ kernel u*R := by
    intro u hu
    have hw : |-z*u| ≤ 2*|z| := by
      rw [abs_mul,abs_neg,abs_of_nonneg hu.1]
      nlinarith [abs_nonneg z,hu.2]
    have hn : 0 < (n:ℝ)+1 := by positivity
    have hadm : |-z*u|/((n:ℝ)+1) ≤ (1/2:ℝ) := by
      apply (div_le_iff₀ hn).mpr
      linarith
    have hb := real_taylor_bound (-z*u) n hadm
    have hpow := pow_le_pow_left₀ (abs_nonneg (-z*u)) hw n
    have hf : 0 ≤ (n.factorial:ℝ) := Nat.cast_nonneg _
    have hb' : |Real.exp (-z*u)-P u| ≤ R := by
      exact hb.trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hpow hf) (by norm_num))
    rw [abs_mul,abs_of_nonneg (kernel_nonnegative u hu)]
    exact mul_le_mul_of_nonneg_left hb' (kernel_nonnegative u hu)
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun u : ℝ => kernel u*(Real.exp (-z*u)-P u)) (a := 0) (b := 2) (by norm_num)
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 2)
    ((hdiff.norm).intervalIntegrable 0 2) ((hg.mul continuous_const).intervalIntegrable 0 2)
    (by intro u hu; simpa only [Real.norm_eq_abs] using hpoint u hu)
  have hbound : |∫ u in (0:ℝ)..2, kernel u*(Real.exp (-z*u)-P u)| ≤ (8/9:ℝ)*R := by
    have h := hnorm.trans hmono
    change |∫ u in (0:ℝ)..2, kernel u*(Real.exp (-z*u)-P u)| ≤
      ∫ u in (0:ℝ)..2, kernel u*R at h
    rw [intervalIntegral.integral_mul_const,kernel_mass] at h
    simpa only [Real.norm_eq_abs] using h
  have hlin : (∫ u in (0:ℝ)..2, kernel u*(Real.exp (-z*u)-P u)) =
      (∫ u in (0:ℝ)..2, kernel u*Real.exp (-z*u)) -
      ∑ k ∈ Finset.range n, ((-z)^k/(k.factorial:ℝ))*
        (∫ u in (0:ℝ)..2, kernel u*u^k) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub (he.intervalIntegrable 0 2) (hpoly.intervalIntegrable 0 2)]
    exact congrArg (fun q => (∫ u in (0:ℝ)..2, kernel u*Real.exp (-z*u))-q) (polynomial_integral n z)
  rw [hlin] at hbound
  simp_rw [kernel,moment_formula] at hbound
  convert hbound using 1
  dsimp [R]
  ring

#print axioms solution
