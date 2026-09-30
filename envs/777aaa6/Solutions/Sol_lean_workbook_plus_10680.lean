-- Prove2me | solution 1 for lean_workbook_plus_10680
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:16:50.26982+00:00
-- url     : https://prove2.me/submissions/610d055e-771f-448c-9318-c7d6040031dd

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable def binomialWeight (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

theorem binomial_weight_pgf (n : ℕ) (p s : ℝ) :
    ∑ k ∈ range (n + 1), binomialWeight n p k * s ^ k = (1 - p + p * s) ^ n := by
  rw [add_comm (1 - p), add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [binomialWeight, mul_pow]
  ring

theorem binomial_affine_power_derivatives (n m : ℕ) (p s : ℝ) :
    iteratedDeriv m (fun t : ℝ => (1 - p + p * t) ^ n) s =
      (n.descFactorial m : ℝ) * p ^ m * (1 - p + p * s) ^ (n - m) := by
  have hc : ContDiff ℝ m (fun z : ℝ => (1 - p + z) ^ n) :=
    (contDiff_const.add contDiff_id).pow n
  rw [show (fun t : ℝ => (1 - p + p * t) ^ n) =
    (fun t : ℝ => (fun z : ℝ => (1 - p + z) ^ n) (p * t)) from rfl]
  rw [iteratedDeriv_comp_const_mul hc p,
    iteratedDeriv_comp_const_add m (fun z : ℝ => z ^ n) (1 - p)]
  simp only [iteratedDeriv_pow]
  ring

theorem binomial_weight_factorial_moment (n m : ℕ) (p : ℝ) :
    ∑ k ∈ range (n + 1), binomialWeight n p k * (k.descFactorial m : ℝ) =
      (n.descFactorial m : ℝ) * p ^ m := by
  have hpoly : (fun s : ℝ => ∑ k ∈ range (n + 1), binomialWeight n p k * s ^ k) =
      (fun s : ℝ => (1 - p + p * s) ^ n) := funext (binomial_weight_pgf n p)
  have hderiv := congrArg (fun f : ℝ → ℝ => iteratedDeriv m f 1) hpoly
  change iteratedDeriv m (fun s : ℝ => ∑ k ∈ range (n + 1), binomialWeight n p k * s ^ k) 1 =
    iteratedDeriv m (fun s : ℝ => (1 - p + p * s) ^ n) 1 at hderiv
  rw [iteratedDeriv_fun_sum (f := fun k s => binomialWeight n p k * s ^ k)
    (fun k _ => (contDiff_const.mul (contDiff_id.pow k)).contDiffAt)] at hderiv
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow, one_pow, mul_one] at hderiv
  rw [binomial_affine_power_derivatives] at hderiv
  simpa only [mul_one, sub_add_cancel, one_pow] using hderiv

theorem binomial_pmf_mass (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (i : Fin (n + 1)) :
    (PMF.binomial p hp n i).toReal = binomialWeight n p i := by
  rw [PMF.binomial_apply]
  have hp' : (p : ENNReal) ≤ 1 := by exact_mod_cast hp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
    ENNReal.toReal_natCast, ENNReal.toReal_sub_of_le hp' ENNReal.one_ne_top,
    ENNReal.toReal_one, Fin.val_last, binomialWeight]
  ring

theorem binomial_pmf_integral (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (f : ℕ → ℝ) :
    (∫ i : Fin (n + 1), f i ∂(PMF.binomial p hp n).toMeasure) =
      ∑ k ∈ range (n + 1), binomialWeight n p k * f k := by
  rw [PMF.integral_eq_sum]
  simp only [binomial_pmf_mass, smul_eq_mul]
  exact Fin.sum_univ_eq_sum_range (fun k => binomialWeight n p k * f k) (n + 1)

theorem binomial_pmf_factorial_moment (n m : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    (∫ i : Fin (n + 1), ((i : ℕ).descFactorial m : ℝ) ∂(PMF.binomial p hp n).toMeasure) =
      (n.descFactorial m : ℝ) * (p : ℝ) ^ m := by
  rw [binomial_pmf_integral n p hp (fun k => (k.descFactorial m : ℝ)),
    binomial_weight_factorial_moment]

theorem binomial_pmf_mean (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    (∫ i : Fin (n + 1), (i : ℝ) ∂(PMF.binomial p hp n).toMeasure) = n * (p : ℝ) := by
  simpa only [Nat.descFactorial_one, pow_one] using binomial_pmf_factorial_moment n 1 p hp

theorem cast_descFactorial_two (n : ℕ) :
    (n.descFactorial 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  cases n with
  | zero => norm_num
  | succ n =>
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
      Nat.succ_sub_succ_eq_sub, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_one]
    ring

theorem binomial_pmf_second_moment (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    (∫ i : Fin (n + 1), (i : ℝ) ^ 2 ∂(PMF.binomial p hp n).toMeasure) =
      (n : ℝ) * (n - 1) * (p : ℝ) ^ 2 + n * p := by
  have heq : (fun i : Fin (n + 1) => (i : ℝ) ^ 2) =
      (fun i : Fin (n + 1) => ((i : ℕ).descFactorial 2 : ℝ) + (i : ℝ)) := by
    funext i
    rw [cast_descFactorial_two]
    ring
  rw [heq, integral_add (Integrable.of_finite) (Integrable.of_finite),
    binomial_pmf_factorial_moment, binomial_pmf_mean, cast_descFactorial_two]

theorem binomial_pmf_variance (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    variance (fun i : Fin (n + 1) => (i : ℝ)) (PMF.binomial p hp n).toMeasure =
      n * (p : ℝ) * (1 - p) := by
  have hmem : MemLp (fun i : Fin (n + 1) => (i : ℝ)) 2 (PMF.binomial p hp n).toMeasure :=
    (memLp_two_iff_integrable_sq (Measurable.aestronglyMeasurable (measurable_of_finite _))).mpr
      Integrable.of_finite
  rw [variance_eq_sub hmem]
  dsimp only [Pi.pow_apply]
  rw [binomial_pmf_second_moment, binomial_pmf_mean]
  ring

theorem binomial_fair_even_mean_variance (m : ℕ) :
    (∫ i : Fin (2 * m + 1), (i : ℝ)
      ∂(PMF.binomial (1 / 2) (by norm_num) (2 * m)).toMeasure) = m ∧
    variance (fun i : Fin (2 * m + 1) => (i : ℝ))
      (PMF.binomial (1 / 2) (by norm_num) (2 * m)).toMeasure = (m : ℝ) / 2 := by
  rw [binomial_pmf_mean, binomial_pmf_variance]
  push_cast
  constructor <;> ring

theorem solution (m : ℕ) : ∃ n : ℕ, n = 2 * m ∧ ∃ p : ℝ, p = 1 / 2 ∧
    ∃ μ : ℝ, μ = n * p ∧ ∃ σ : ℝ, σ ^ 2 = n * p * (1 - p) := by
  refine ⟨2 * m, rfl, 1 / 2, rfl, m, ?_, Real.sqrt ((m : ℝ) / 2), ?_⟩
  · push_cast
    ring
  · rw [Real.sq_sqrt (by positivity)]
    push_cast
    ring

#print axioms binomialWeight
#print axioms binomial_weight_pgf
#print axioms binomial_affine_power_derivatives
#print axioms binomial_weight_factorial_moment
#print axioms binomial_pmf_mass
#print axioms binomial_pmf_integral
#print axioms binomial_pmf_factorial_moment
#print axioms binomial_pmf_mean
#print axioms cast_descFactorial_two
#print axioms binomial_pmf_second_moment
#print axioms binomial_pmf_variance
#print axioms binomial_fair_even_mean_variance
#print axioms solution
