-- Prove2me | solution 1 for Martingale.clt_of_mds_array
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:46:11.154179+00:00
-- url     : https://prove2.me/submissions/dcfee6a0-7e9f-4698-9eb1-956a202f4d49

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real

/- Finite-product martingale-array CLT. Product/Taylor by the root agent;
stopping, quantitative convergence, finite maximum, and conclusion by truncation_resume.
The classical argument follows McLeish, as presented in the credited Valko/Sethuraman note. -/

section Component1
open scoped BigOperators

namespace MdsProduct

lemma linear_factor_norm_le (x : ℝ) :
    ‖(1 : ℂ) + (x : ℂ) * Complex.I‖ ≤ Real.exp (x ^ 2 / 2) := by
  have hnorm : ‖(1 : ℂ) + (x : ℂ) * Complex.I‖ = Real.sqrt (1 + x ^ 2) := by
    simpa using Complex.norm_add_mul_I (1 : ℝ) x
  rw [hnorm]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨(Real.exp_pos _).le, ?_⟩
  have he : Real.exp (x ^ 2 / 2) ^ 2 = Real.exp (x ^ 2) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  linarith [Real.add_one_le_exp (x ^ 2)]

lemma linear_product_norm_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ‖∏ i ∈ s, ((1 : ℂ) + (x i : ℂ) * Complex.I)‖ ≤
      Real.exp ((∑ i ∈ s, x i ^ 2) / 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, norm_mul, add_div, Real.exp_add]
    exact mul_le_mul (linear_factor_norm_le (x a)) ih (norm_nonneg _) (Real.exp_pos _).le

lemma product_sub_one_norm_le {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ ≤ 1) :
    ‖(∏ i ∈ s, z i) - 1‖ ≤ ∑ i ∈ s, ‖z i - 1‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hid : z a * (∏ i ∈ s, z i) - 1 =
        (z a - 1) + z a * ((∏ i ∈ s, z i) - 1) := by ring
    rw [hid]
    calc
      _ ≤ ‖z a - 1‖ + ‖z a * ((∏ i ∈ s, z i) - 1)‖ := norm_add_le _ _
      _ = ‖z a - 1‖ + ‖z a‖ * ‖(∏ i ∈ s, z i) - 1‖ := by rw [norm_mul]
      _ ≤ ‖z a - 1‖ + 1 * (∑ i ∈ s, ‖z i - 1‖) := by
        gcongr
        · exact hz a (Finset.mem_insert_self _ _)
        · exact ih (fun i hi => hz i (Finset.mem_insert_of_mem hi))
      _ = _ := by ring

end MdsProduct
end Component1

section Component2
open scoped BigOperators

namespace MdsProduct

noncomputable def phase (x : ℝ) : ℂ := (x : ℂ) * Complex.I + (x ^ 2 / 2 : ℝ)

noncomputable def normalizedFactor (x : ℝ) : ℂ :=
  ((1 : ℂ) + (x : ℂ) * Complex.I) * Complex.exp (-phase x)

lemma phase_re (x : ℝ) : (phase x).re = x ^ 2 / 2 := by
  simp [phase, sq, Complex.mul_re]

lemma normalized_factor_norm_le (x : ℝ) : ‖normalizedFactor x‖ ≤ 1 := by
  have hre : (-phase x).re = -(x ^ 2 / 2) := by simp only [Complex.neg_re, phase_re]
  rw [normalizedFactor, norm_mul, Complex.norm_exp, hre]
  calc
    _ ≤ Real.exp (x ^ 2 / 2) * Real.exp (-(x ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_right (linear_factor_norm_le x) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

lemma phase_norm_le {x : ℝ} (hx : |x| ≤ 1) : ‖phase x‖ ≤ 2 * |x| := by
  have hsq : x ^ 2 ≤ |x| := by
    nlinarith [sq_abs x, mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hx)]
  calc
    _ ≤ ‖(x : ℂ) * Complex.I‖ + ‖((x ^ 2 / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = |x| + x ^ 2 / 2 := by simp
    _ ≤ _ := by linarith [abs_nonneg x]

lemma linear_exp_error {x : ℝ} (hx : |x| ≤ 1) :
    ‖((1 : ℂ) + (x : ℂ) * Complex.I) - Complex.exp (phase x)‖ ≤
      (8 * Real.exp 2 + 1) * |x| ^ 3 := by
  let w := phase x
  let poly : ℂ := 1 + w + w ^ 2 / 2
  have hnorm : ‖w‖ ≤ 2 * |x| := phase_norm_le hx
  have hnorm2 : ‖w‖ ≤ 2 := by linarith
  have hseries : (∑ m ∈ Finset.range 3, w ^ m / (m.factorial : ℂ)) = poly := by
    norm_num [Finset.sum_range_succ, Nat.factorial, poly]
  have htail := Complex.norm_exp_sub_sum_le_norm_mul_exp w 3
  rw [hseries] at htail
  have htail' : ‖Complex.exp w - poly‖ ≤ 8 * Real.exp 2 * |x| ^ 3 := by
    calc
      _ ≤ ‖w‖ ^ 3 * Real.exp ‖w‖ := htail
      _ ≤ (2 * |x|) ^ 3 * Real.exp 2 := by gcongr
      _ = _ := by ring
  have hpoly : poly - ((1 : ℂ) + (x : ℂ) * Complex.I) =
      ((x ^ 3 / 2 : ℝ) : ℂ) * Complex.I + ((x ^ 4 / 8 : ℝ) : ℂ) := by
    dsimp [poly, w, phase]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  have hpow4 : |x| ^ 4 ≤ |x| ^ 3 := by
    simpa [pow_succ] using mul_le_mul_of_nonneg_left hx (pow_nonneg (abs_nonneg x) 3)
  have hpolybound : ‖poly - ((1 : ℂ) + (x : ℂ) * Complex.I)‖ ≤ |x| ^ 3 := by
    rw [hpoly]
    calc
      _ ≤ ‖((x ^ 3 / 2 : ℝ) : ℂ) * Complex.I‖ + ‖((x ^ 4 / 8 : ℝ) : ℂ)‖ :=
        norm_add_le _ _
      _ = |x| ^ 3 / 2 + |x| ^ 4 / 8 := by simp
      _ ≤ _ := by nlinarith [pow_nonneg (abs_nonneg x) 3]
  rw [norm_sub_rev]
  calc
    _ ≤ ‖Complex.exp w - poly‖ + ‖poly - ((1 : ℂ) + (x : ℂ) * Complex.I)‖ := by
      have hid : Complex.exp w - ((1 : ℂ) + (x : ℂ) * Complex.I) =
          (Complex.exp w - poly) + (poly - ((1 : ℂ) + (x : ℂ) * Complex.I)) := by ring
      rw [hid]
      exact norm_add_le _ _
    _ ≤ 8 * Real.exp 2 * |x| ^ 3 + |x| ^ 3 := add_le_add htail' hpolybound
    _ = _ := by ring

lemma normalized_factor_error {x : ℝ} (hx : |x| ≤ 1) :
    ‖normalizedFactor x - 1‖ ≤ (8 * Real.exp 2 + 1) * |x| ^ 3 := by
  have hexp : Complex.exp (phase x) * Complex.exp (-phase x) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hid : normalizedFactor x - 1 =
      (((1 : ℂ) + (x : ℂ) * Complex.I) - Complex.exp (phase x)) *
        Complex.exp (-phase x) := by
    rw [sub_mul, hexp]
    rfl
  have hnorm : ‖Complex.exp (-phase x)‖ ≤ 1 := by
    rw [Complex.norm_exp, Complex.neg_re, phase_re]
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (by positivity)
  rw [hid, norm_mul]
  calc
    _ ≤ ‖((1 : ℂ) + (x : ℂ) * Complex.I) - Complex.exp (phase x)‖ * 1 :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ ≤ _ := by simpa using linear_exp_error hx

lemma normalized_product_error {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {M : ℝ} (hM : ∀ i ∈ s, |x i| ≤ M) (hM1 : M ≤ 1) :
    ‖(∏ i ∈ s, normalizedFactor (x i)) - 1‖ ≤
      (8 * Real.exp 2 + 1) * M * (∑ i ∈ s, x i ^ 2) := by
  have hC : 0 ≤ 8 * Real.exp 2 + 1 := by positivity
  calc
    _ ≤ ∑ i ∈ s, ‖normalizedFactor (x i) - 1‖ :=
      product_sub_one_norm_le s (fun i => normalizedFactor (x i))
        (fun i _ => normalized_factor_norm_le (x i))
    _ ≤ ∑ i ∈ s, (8 * Real.exp 2 + 1) * M * x i ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ (8 * Real.exp 2 + 1) * |x i| ^ 3 :=
          normalized_factor_error ((hM i hi).trans hM1)
        _ = (8 * Real.exp 2 + 1) * |x i| * x i ^ 2 := by
          rw [pow_succ, sq_abs]
          ring
        _ ≤ _ := by gcongr; exact hM i hi
    _ = _ := by rw [Finset.mul_sum]

lemma linear_product_error {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {M : ℝ} (hM : ∀ i ∈ s, |x i| ≤ M) (hM1 : M ≤ 1) :
    ‖(∏ i ∈ s, ((1 : ℂ) + (x i : ℂ) * Complex.I)) -
        Complex.exp (∑ i ∈ s, phase (x i))‖ ≤
      Real.exp ((∑ i ∈ s, x i ^ 2) / 2) *
        ((8 * Real.exp 2 + 1) * M * (∑ i ∈ s, x i ^ 2)) := by
  have hprod : (∏ i ∈ s, normalizedFactor (x i)) *
      Complex.exp (∑ i ∈ s, phase (x i)) =
      ∏ i ∈ s, ((1 : ℂ) + (x i : ℂ) * Complex.I) := by
    simp only [normalizedFactor, Finset.prod_mul_distrib]
    rw [← Complex.exp_sum, Finset.sum_neg_distrib, mul_assoc,
      ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have hid : (∏ i ∈ s, ((1 : ℂ) + (x i : ℂ) * Complex.I)) -
      Complex.exp (∑ i ∈ s, phase (x i)) =
      ((∏ i ∈ s, normalizedFactor (x i)) - 1) *
        Complex.exp (∑ i ∈ s, phase (x i)) := by
    rw [sub_mul, hprod, one_mul]
  have hre : (∑ i ∈ s, phase (x i)).re = (∑ i ∈ s, x i ^ 2) / 2 := by
    simp [phase_re, Finset.sum_div]
  rw [hid, norm_mul, Complex.norm_exp, hre]
  calc
    _ ≤ ((8 * Real.exp 2 + 1) * M * (∑ i ∈ s, x i ^ 2)) *
        Real.exp ((∑ i ∈ s, x i ^ 2) / 2) :=
      mul_le_mul_of_nonneg_right (normalized_product_error s x hM hM1) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

end MdsProduct
end Component2

section Component3
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators MeasureTheory ProbabilityTheory

namespace MdsArray

def squareSum (D : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, D j ^ 2

noncomputable def linearProduct (D : ℕ → ℝ) (t : ℝ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range k, ((1 : ℂ) + (t * D j : ℝ) * Complex.I)

noncomputable def stoppedProduct (D : ℕ → ℝ) (C t : ℝ) (k : ℕ) : ℂ := by
  classical
  exact ∏ j ∈ Finset.range k,
    if squareSum D j ≤ C then (1 : ℂ) + (t * D j : ℝ) * Complex.I else 1

noncomputable def activeProduct (D : ℕ → ℝ) (C t : ℝ) (k : ℕ) : ℂ := by
  classical
  exact if squareSum D k ≤ C then stoppedProduct D C t k else 0

noncomputable def stoppedCoefficient (D : ℕ → ℝ) (C t : ℝ) (k : ℕ) : ℂ :=
  (t : ℂ) * Complex.I * activeProduct D C t k

lemma squareSum_nonneg (D : ℕ → ℝ) (k : ℕ) : 0 ≤ squareSum D k := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma squareSum_mono (D : ℕ → ℝ) : Monotone (squareSum D) := by
  intro j k hjk
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjk)
    (fun i _ _ => sq_nonneg (D i))

lemma stoppedProduct_eq_linearProduct (D : ℕ → ℝ) (C t : ℝ) (k : ℕ)
    (hk : squareSum D k ≤ C) : stoppedProduct D C t k = linearProduct D t k := by
  classical
  apply Finset.prod_congr rfl
  intro j hj
  exact if_pos ((squareSum_mono D (Nat.le_of_lt (Finset.mem_range.mp hj))).trans hk)

lemma norm_linearProduct_le (D : ℕ → ℝ) (t : ℝ) (k : ℕ) :
    ‖linearProduct D t k‖ ≤ Real.exp (t ^ 2 * squareSum D k / 2) := by
  have hs : (∑ j ∈ Finset.range k, (t * D j) ^ 2) = t ^ 2 * squareSum D k := by
    simp only [squareSum, mul_pow, Finset.mul_sum]
  simpa only [linearProduct, hs] using
    MdsProduct.linear_product_norm_le (Finset.range k) (fun j => t * D j)

lemma norm_activeProduct_le (D : ℕ → ℝ) (C t : ℝ) (k : ℕ) :
    ‖activeProduct D C t k‖ ≤ Real.exp (t ^ 2 * C / 2) := by
  classical
  by_cases hk : squareSum D k ≤ C
  · rw [activeProduct, if_pos hk, stoppedProduct_eq_linearProduct D C t k hk]
    exact (norm_linearProduct_le D t k).trans (Real.exp_le_exp.mpr (by gcongr))
  · simp only [activeProduct, if_neg hk, norm_zero]
    exact (Real.exp_pos _).le

lemma norm_stoppedCoefficient_le (D : ℕ → ℝ) (C t : ℝ) (k : ℕ) :
    ‖stoppedCoefficient D C t k‖ ≤ |t| * Real.exp (t ^ 2 * C / 2) := by
  simpa [stoppedCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_left (norm_activeProduct_le D C t k) (abs_nonneg t)

lemma stoppedProduct_zero (D : ℕ → ℝ) (C t : ℝ) : stoppedProduct D C t 0 = 1 := by
  simp [stoppedProduct]

lemma stoppedCoefficient_zero (D : ℕ → ℝ) (C t : ℝ) (hC : 0 ≤ C) :
    stoppedCoefficient D C t 0 = (t : ℂ) * Complex.I := by
  simp [stoppedCoefficient, activeProduct, squareSum, stoppedProduct, hC]

lemma stoppedProduct_succ (D : ℕ → ℝ) (C t : ℝ) (k : ℕ) :
    stoppedProduct D C t (k + 1) = stoppedProduct D C t k +
      D k • stoppedCoefficient D C t k := by
  classical
  rw [stoppedProduct, Finset.prod_range_succ]
  change stoppedProduct D C t k *
    (if squareSum D k ≤ C then (1 : ℂ) + (t * D k : ℝ) * Complex.I else 1) = _
  by_cases hk : squareSum D k ≤ C
  · simp only [hk, if_true, stoppedCoefficient, activeProduct, Complex.real_smul,
      Complex.ofReal_mul]
    ring
  · simp [hk, stoppedCoefficient, activeProduct]

lemma norm_stoppedProduct_le (D : ℕ → ℝ) (C t : ℝ) (hC : 0 ≤ C)
    (n : ℕ) {M : ℝ} (hM : 0 ≤ M) (hD : ∀ j < n, |D j| ≤ M) :
    ‖stoppedProduct D C t n‖ ≤ Real.exp (t ^ 2 * C / 2) * (1 + |t| * M) := by
  classical
  induction n with
  | zero =>
    rw [stoppedProduct_zero, norm_one]
    have he : 1 ≤ Real.exp (t ^ 2 * C / 2) := by
      have hn : 0 ≤ t ^ 2 * C / 2 := by positivity
      linarith [Real.add_one_le_exp (t ^ 2 * C / 2)]
    nlinarith [mul_nonneg (abs_nonneg t) hM]
  | succ n ih =>
    by_cases hn : squareSum D n ≤ C
    · have hp : ‖stoppedProduct D C t n‖ ≤ Real.exp (t ^ 2 * C / 2) := by
        rw [stoppedProduct_eq_linearProduct D C t n hn]
        exact (norm_linearProduct_le D t n).trans (Real.exp_le_exp.mpr (by gcongr))
      have hf : ‖(1 : ℂ) + (t * D n : ℝ) * Complex.I‖ ≤ 1 + |t| * M := by
        calc
          _ ≤ ‖(1 : ℂ)‖ + ‖(t * D n : ℝ) * Complex.I‖ := norm_add_le _ _
          _ = 1 + |t| * |D n| := by simp
          _ ≤ 1 + |t| * M := by gcongr; exact hD n (Nat.lt_succ_self n)
      rw [stoppedProduct, Finset.prod_range_succ]
      change ‖stoppedProduct D C t n *
        (if squareSum D n ≤ C then (1 : ℂ) + (t * D n : ℝ) * Complex.I else 1)‖ ≤ _
      rw [if_pos hn, norm_mul]
      exact mul_le_mul hp hf (norm_nonneg _) (Real.exp_pos _).le
    · have he : stoppedProduct D C t (n + 1) = stoppedProduct D C t n := by
        rw [stoppedProduct_succ]
        simp [stoppedCoefficient, activeProduct, hn]
      rw [he]
      exact ih (fun j hj => hD j (Nat.lt_trans hj (Nat.lt_succ_self n)))

section Measurability

variable {Ω : Type*} {m : MeasurableSpace Ω} {D : ℕ → Ω → ℝ}

lemma measurable_squareSum (k : ℕ) (hD : ∀ j < k, Measurable (D j)) :
    Measurable (fun ω => squareSum (fun j => D j ω) k) := by
  apply Finset.measurable_sum
  intro j hj
  exact (hD j (Finset.mem_range.mp hj)).pow_const 2

lemma measurable_stoppedProduct (C t : ℝ) (k : ℕ)
    (hD : ∀ j < k, Measurable (D j)) :
    Measurable (fun ω => stoppedProduct (fun j => D j ω) C t k) := by
  classical
  apply Finset.measurable_prod
  intro j hj
  have hjk := Finset.mem_range.mp hj
  have hs := measurable_squareSum j (fun i hi => hD i (hi.trans hjk))
  have hdj : Measurable (D j) := hD j hjk
  have hf : Measurable (fun ω => (1 : ℂ) + (t * D j ω : ℝ) * Complex.I) := by
    fun_prop
  exact Measurable.ite (measurableSet_le hs measurable_const) hf measurable_const

lemma measurable_activeProduct (C t : ℝ) (k : ℕ)
    (hD : ∀ j < k, Measurable (D j)) :
    Measurable (fun ω => activeProduct (fun j => D j ω) C t k) := by
  classical
  exact Measurable.ite (measurableSet_le (measurable_squareSum k hD) measurable_const)
    (measurable_stoppedProduct C t k hD) measurable_const

lemma measurable_stoppedCoefficient (C t : ℝ) (k : ℕ)
    (hD : ∀ j < k, Measurable (D j)) :
    Measurable (fun ω => stoppedCoefficient (fun j => D j ω) C t k) := by
  exact measurable_const.mul (measurable_activeProduct C t k hD)

end Measurability

section Integrals

variable {Ω : Type*} {m0 : MeasurableSpace Ω}
  (P : Measure Ω) [IsProbabilityMeasure P] (D : ℕ → Ω → ℝ)

omit [IsProbabilityMeasure P] in
lemma integrable_stoppedIncrement (C t : ℝ) (k : ℕ)
    (hmeas : ∀ j, Measurable (D j)) (hint : Integrable (D k) P) :
    Integrable (fun ω => D k ω • stoppedCoefficient (fun j => D j ω) C t k) P := by
  exact hint.smul_bdd (|t| * Real.exp (t ^ 2 * C / 2))
    (measurable_stoppedCoefficient C t k (fun j _ => hmeas j)).aestronglyMeasurable
    (ae_of_all P fun ω => norm_stoppedCoefficient_le (fun j => D j ω) C t k)

lemma integrable_stoppedProduct (C t : ℝ) (n : ℕ)
    (hmeas : ∀ j, Measurable (D j)) (hint : ∀ j, Integrable (D j) P) :
    Integrable (fun ω => stoppedProduct (fun j => D j ω) C t n) P := by
  induction n with
  | zero => simpa only [stoppedProduct_zero] using (integrable_const (1 : ℂ))
  | succ n ih =>
    simpa only [stoppedProduct_succ] using
      ih.add (integrable_stoppedIncrement P D C t n hmeas (hint n))

lemma integral_stoppedIncrement_succ_eq_zero (ℱ : Filtration ℕ m0)
    (C t : ℝ) (k : ℕ)
    (hadapt : ∀ j, Measurable[ℱ j] (D j))
    (hint : Integrable (D (k + 1)) P)
    (hmds : P[D (k + 1) | ℱ k] =ᵐ[P] 0) :
    ∫ ω, D (k + 1) ω • stoppedCoefficient (fun j => D j ω) C t (k + 1) ∂P = 0 := by
  have hmeas : ∀ j, Measurable (D j) := fun j =>
    (hadapt j).mono (ℱ.le j) le_rfl
  have hcoef : Measurable[ℱ k]
      (fun ω => stoppedCoefficient (fun j => D j ω) C t (k + 1)) := by
    exact measurable_stoppedCoefficient C t (k + 1)
      (fun j hj => (hadapt j).mono (ℱ.mono (Nat.le_of_lt_succ hj)) le_rfl)
  have hi := integrable_stoppedIncrement P D C t (k + 1) hmeas hint
  have hce := condExp_smul_of_aestronglyMeasurable_right hint hi
    hcoef.aestronglyMeasurable
  calc
    _ = ∫ ω, (P[fun ω => D (k + 1) ω •
        stoppedCoefficient (fun j => D j ω) C t (k + 1) | ℱ k]) ω ∂P :=
      (integral_condExp (ℱ.le k)).symm
    _ = ∫ _ω, (0 : ℂ) ∂P := by
      apply integral_congr_ae
      filter_upwards [hce, hmds] with ω hω hz
      simpa [hz] using hω
    _ = 0 := integral_zero _ _

lemma integral_stoppedProduct_eq_one (ℱ : Filtration ℕ m0)
    (C t : ℝ) (hC : 0 ≤ C) (n : ℕ)
    (hadapt : ∀ j, Measurable[ℱ j] (D j))
    (hint : ∀ j, Integrable (D j) P)
    (hmds : ∀ j, P[D (j + 1) | ℱ j] =ᵐ[P] 0)
    (hcent : ∫ ω, D 0 ω ∂P = 0) :
    ∫ ω, stoppedProduct (fun j => D j ω) C t n ∂P = 1 := by
  have hmeas : ∀ j, Measurable (D j) := fun j =>
    (hadapt j).mono (ℱ.le j) le_rfl
  induction n with
  | zero => simp [stoppedProduct_zero]
  | succ n ih =>
    simp_rw [stoppedProduct_succ]
    rw [integral_add (integrable_stoppedProduct P D C t n hmeas hint)
      (integrable_stoppedIncrement P D C t n hmeas (hint n)), ih]
    suffices (∫ ω, D n ω • stoppedCoefficient (fun j => D j ω) C t n ∂P) = 0 by
      rw [this, add_zero]
    cases n with
    | zero => simp_rw [stoppedCoefficient_zero _ C t hC]
              rw [integral_smul_const, hcent, zero_smul]
    | succ k => exact integral_stoppedIncrement_succ_eq_zero P D ℱ C t k hadapt
                  (hint (k + 1)) (hmds k)

end Integrals

end MdsArray
end Component3

section Component4
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators MeasureTheory ProbabilityTheory Topology

namespace MdsArray

noncomputable def phaseValue (D : ℕ → ℝ) (t v : ℝ) (n : ℕ) : ℂ :=
  (Real.exp (t ^ 2 * v / 2) : ℂ) *
    Complex.exp ((t * ∑ j ∈ Finset.range n, D j : ℝ) * Complex.I)

noncomputable def errorScale (t v : ℝ) : ℝ :=
  Real.exp (t ^ 2 * (v + 1) / 2) *
    ((8 * Real.exp 2 + 1) * |t| * (t ^ 2 * (v + 1)) + 3 * |t|)

lemma norm_phaseValue (D : ℕ → ℝ) (t v : ℝ) (n : ℕ) :
    ‖phaseValue D t v n‖ = Real.exp (t ^ 2 * v / 2) := by
  have hu : ‖Complex.exp ((t * ∑ j ∈ Finset.range n, D j : ℝ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [phaseValue, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), hu, mul_one]

lemma norm_phaseValue_sub (D : ℕ → ℝ) (t v w : ℝ) (n : ℕ) :
    ‖phaseValue D t v n - phaseValue D t w n‖ =
      |Real.exp (t ^ 2 * v / 2) - Real.exp (t ^ 2 * w / 2)| := by
  have hu : ‖Complex.exp ((t * ∑ j ∈ Finset.range n, D j : ℝ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [phaseValue, phaseValue, ← sub_mul, norm_mul, hu, mul_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

lemma exp_sum_phase_eq (D : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    Complex.exp (∑ j ∈ Finset.range n, MdsProduct.phase (t * D j)) =
      phaseValue D t (squareSum D n) n := by
  have hs : (∑ j ∈ Finset.range n, MdsProduct.phase (t * D j)) =
      ((t * ∑ j ∈ Finset.range n, D j : ℝ) : ℂ) * Complex.I +
        ((t ^ 2 * squareSum D n / 2 : ℝ) : ℂ) := by
    simp only [MdsProduct.phase, Finset.sum_add_distrib, squareSum, mul_pow,
      Finset.mul_sum, Finset.sum_div, Complex.ofReal_sum, Complex.ofReal_mul,
      Finset.sum_mul]
  rw [hs, Complex.exp_add, ← Complex.ofReal_exp, phaseValue, mul_comm]

lemma stopped_error_good (D : ℕ → ℝ) (t v : ℝ)
    (n : ℕ) {M ε : ℝ} (hM : 0 ≤ M) (hD : ∀ j < n, |D j| ≤ M)
    (hsmall : |t| * M ≤ 1) (hQ : squareSum D n ≤ v + 1)
    (hamp : |Real.exp (t ^ 2 * squareSum D n / 2) -
      Real.exp (t ^ 2 * v / 2)| ≤ ε) :
    ‖stoppedProduct D (v + 1) t n - phaseValue D t v n‖ ≤
      Real.exp (t ^ 2 * (v + 1) / 2) *
        ((8 * Real.exp 2 + 1) * |t| * (t ^ 2 * (v + 1))) * M + ε := by
  have hx : ∀ j ∈ Finset.range n, |t * D j| ≤ |t| * M := by
    intro j hj
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hD j (Finset.mem_range.mp hj)) (abs_nonneg t)
  have hs : (∑ j ∈ Finset.range n, (t * D j) ^ 2) = t ^ 2 * squareSum D n := by
    simp only [squareSum, mul_pow, Finset.mul_sum]
  have hTaylor := MdsProduct.linear_product_error (Finset.range n)
    (fun j => t * D j) hx hsmall
  rw [exp_sum_phase_eq, hs] at hTaylor
  have hQnonneg := squareSum_nonneg D n
  have he : ‖linearProduct D t n - phaseValue D t (squareSum D n) n‖ ≤
      Real.exp (t ^ 2 * (v + 1) / 2) *
        ((8 * Real.exp 2 + 1) * |t| * (t ^ 2 * (v + 1))) * M := by
    calc
      _ ≤ Real.exp (t ^ 2 * squareSum D n / 2) *
          ((8 * Real.exp 2 + 1) * (|t| * M) * (t ^ 2 * squareSum D n)) := hTaylor
      _ ≤ Real.exp (t ^ 2 * (v + 1) / 2) *
          ((8 * Real.exp 2 + 1) * (|t| * M) * (t ^ 2 * (v + 1))) := by
        gcongr
      _ = _ := by ring
  rw [stoppedProduct_eq_linearProduct D (v + 1) t n hQ]
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add he (by simpa only [norm_phaseValue_sub] using hamp))

lemma stopped_error_bound (D : ℕ → ℝ) (t v : ℝ) (hv : 0 ≤ v)
    (n : ℕ) {M ε δ : ℝ} (hM : 0 ≤ M) (hD : ∀ j < n, |D j| ≤ M)
    (hε : 0 ≤ ε) (hδ : δ ≤ 1)
    (hamp : ∀ q : ℝ, |q - v| < δ →
      |Real.exp (t ^ 2 * q / 2) - Real.exp (t ^ 2 * v / 2)| ≤ ε) :
    ‖stoppedProduct D (v + 1) t n - phaseValue D t v n‖ ≤
      ε + errorScale t v * M +
        (if δ ≤ |squareSum D n - v| then 2 * Real.exp (t ^ 2 * (v + 1) / 2) else 0) := by
  classical
  let B := Real.exp (t ^ 2 * (v + 1) / 2)
  let K := B * ((8 * Real.exp 2 + 1) * |t| * (t ^ 2 * (v + 1)))
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have hK : 0 ≤ K := by dsimp [K, B]; positivity
  have hA : errorScale t v = K + 3 * B * |t| := by
    dsimp [errorScale, K, B]
    ring
  have hglobal : ‖stoppedProduct D (v + 1) t n - phaseValue D t v n‖ ≤
      2 * B + B * |t| * M := by
    have hp := norm_stoppedProduct_le D (v + 1) t (by linarith) n hM hD
    have he : ‖phaseValue D t v n‖ ≤ B := by
      rw [norm_phaseValue]
      apply Real.exp_le_exp.mpr
      dsimp [B]
      gcongr
      linarith
    calc
      _ ≤ ‖stoppedProduct D (v + 1) t n‖ + ‖phaseValue D t v n‖ := norm_sub_le _ _
      _ ≤ B * (1 + |t| * M) + B := add_le_add hp he
      _ = _ := by ring
  by_cases hbad : δ ≤ |squareSum D n - v|
  · rw [if_pos hbad, hA]
    dsimp [B] at hglobal ⊢
    nlinarith [mul_nonneg hK hM, mul_nonneg (mul_nonneg hB (abs_nonneg t)) hM]
  · rw [if_neg hbad, add_zero, hA]
    have hclose : |squareSum D n - v| < δ := lt_of_not_ge hbad
    have hQ : squareSum D n ≤ v + 1 := by
      have := (abs_lt.mp hclose).2
      linarith
    by_cases hsmall : |t| * M ≤ 1
    · have hgood := stopped_error_good D t v n hM hD hsmall hQ
        (hamp (squareSum D n) hclose)
      change ‖stoppedProduct D (v + 1) t n - phaseValue D t v n‖ ≤ K * M + ε at hgood
      nlinarith [mul_nonneg (mul_nonneg hB (abs_nonneg t)) hM]
    · have hm : 1 < |t| * M := lt_of_not_ge hsmall
      nlinarith [mul_nonneg hK hM, mul_nonneg hB (le_of_lt (sub_pos.mpr hm))]

section IntegralConvergence

variable {Ω : Type*} {m0 : MeasurableSpace Ω}
  (P : Measure Ω) [IsProbabilityMeasure P]
  (D : ℕ → ℕ → Ω → ℝ) (M : ℕ → Ω → ℝ)

lemma integrable_phaseValue (t v : ℝ) (n : ℕ)
    (hmeas : ∀ k, Measurable (D n k)) :
    Integrable (fun ω => phaseValue (fun j => D n j ω) t v n) P := by
  have hs : Measurable (fun ω => ∑ j ∈ Finset.range n, D n j ω) := by
    exact Finset.measurable_sum _ (fun j _ => hmeas j)
  have hm : Measurable (fun ω => phaseValue (fun j => D n j ω) t v n) := by
    unfold phaseValue
    fun_prop
  exact (integrable_const (Real.exp (t ^ 2 * v / 2))).mono' hm.aestronglyMeasurable
    (ae_of_all P fun ω => (norm_phaseValue (fun j => D n j ω) t v n).le)

lemma tendsto_integral_stopped_error (t v : ℝ) (hv : 0 ≤ v)
    (hmeas : ∀ n k, Measurable (D n k))
    (hint : ∀ n k, Integrable (D n k) P)
    (hMnonneg : ∀ n ω, 0 ≤ M n ω)
    (hMbound : ∀ n k, k < n → ∀ ω, |D n k ω| ≤ M n ω)
    (hMint : ∀ n, Integrable (M n) P)
    (hMlim : Tendsto (fun n => ∫ ω, M n ω ∂P) atTop (𝓝 0))
    (hvar : TendstoInMeasure P
      (fun n ω => squareSum (fun j => D n j ω) n) atTop (fun _ => v)) :
    Tendsto (fun n => ∫ ω, stoppedProduct (fun j => D n j ω) (v + 1) t n -
      phaseValue (fun j => D n j ω) t v n ∂P) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hc : Continuous (fun q : ℝ => Real.exp (t ^ 2 * q / 2)) := by fun_prop
  obtain ⟨r, hr, hamp⟩ := Metric.continuousAt_iff.mp hc.continuousAt (ε / 2) (by positivity)
  let δ := min r 1
  have hδ : 0 < δ := lt_min hr zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hamp' : ∀ q : ℝ, |q - v| < δ →
      |Real.exp (t ^ 2 * q / 2) - Real.exp (t ^ 2 * v / 2)| ≤ ε / 2 := by
    intro q hq
    have hh := hamp (show dist q v < r by
      simpa only [Real.dist_eq] using hq.trans_le (min_le_left r 1))
    simpa only [Real.dist_eq] using hh.le
  let bad : ℕ → Set Ω := fun n => {ω | δ ≤ |squareSum (fun j => D n j ω) n - v|}
  have hbadmeas : ∀ n, MeasurableSet (bad n) := by
    intro n
    have hq : Measurable (fun ω => squareSum (fun j => D n j ω) n - v) :=
      (measurable_squareSum n (fun j _ => hmeas n j)).sub measurable_const
    exact measurableSet_le measurable_const hq.abs
  have hbadlim : Tendsto (fun n => P.real (bad n)) atTop (𝓝 0) := by
    simpa only [bad, Real.norm_eq_abs] using
      (tendstoInMeasure_iff_measureReal_norm.mp hvar) δ hδ
  let B := Real.exp (t ^ 2 * (v + 1) / 2)
  let A := errorScale t v
  have hupperlim : Tendsto
      (fun n => ε / 2 + A * (∫ ω, M n ω ∂P) + (2 * B) * P.real (bad n))
      atTop (𝓝 (ε / 2)) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul hMlim)).add
      (tendsto_const_nhds.mul hbadlim)
  have hevent : ∀ᶠ n in atTop,
      ε / 2 + A * (∫ ω, M n ω ∂P) + (2 * B) * P.real (bad n) < ε :=
    hupperlim.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hevent] with n hn
  have herrorint : Integrable (fun ω =>
      stoppedProduct (fun j => D n j ω) (v + 1) t n -
        phaseValue (fun j => D n j ω) t v n) P :=
    (integrable_stoppedProduct P (D n) (v + 1) t n (hmeas n) (hint n)).sub
      (integrable_phaseValue P D t v n (hmeas n))
  have hbind : Integrable ((bad n).indicator (fun _ : Ω => 2 * B)) P :=
    (integrable_const (2 * B)).indicator (hbadmeas n)
  have hfirst : Integrable (fun ω => ε / 2 + A * M n ω) P :=
    (integrable_const (ε / 2)).add ((hMint n).const_mul A)
  have hpoint : ∀ ω, ‖stoppedProduct (fun j => D n j ω) (v + 1) t n -
      phaseValue (fun j => D n j ω) t v n‖ ≤
      ε / 2 + A * M n ω + (bad n).indicator (fun _ : Ω => 2 * B) ω := by
    intro ω
    simpa only [A, B, bad, Set.indicator, Set.mem_setOf_eq] using
      stopped_error_bound (fun j => D n j ω) t v hv n (hMnonneg n ω)
        (fun j hj => hMbound n j hj ω) (by positivity : 0 ≤ ε / 2) hδ1 hamp'
  have hupper : ‖∫ ω, stoppedProduct (fun j => D n j ω) (v + 1) t n -
      phaseValue (fun j => D n j ω) t v n ∂P‖ ≤
      ε / 2 + A * (∫ ω, M n ω ∂P) + (2 * B) * P.real (bad n) := by
    calc
      _ ≤ ∫ ω, ‖stoppedProduct (fun j => D n j ω) (v + 1) t n -
          phaseValue (fun j => D n j ω) t v n‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, ε / 2 + A * M n ω + (bad n).indicator (fun _ : Ω => 2 * B) ω ∂P :=
        integral_mono herrorint.norm (hfirst.add hbind) hpoint
      _ = _ := by
        rw [integral_add hfirst hbind,
          integral_add (integrable_const (ε / 2)) ((hMint n).const_mul A),
          integral_const_mul, integral_indicator_const _ (hbadmeas n)]
        simp [smul_eq_mul, mul_comm]
  simpa only [dist_zero_right] using hupper.trans_lt hn

lemma tendsto_characteristic_integral (ℱ : Filtration ℕ m0) (t v : ℝ) (hv : 0 ≤ v)
    (hadapt : ∀ n k, Measurable[ℱ k] (D n k))
    (hint : ∀ n k, Integrable (D n k) P)
    (hmds : ∀ n k, P[D n (k + 1) | ℱ k] =ᵐ[P] 0)
    (hcent : ∀ n, ∫ ω, D n 0 ω ∂P = 0)
    (hMnonneg : ∀ n ω, 0 ≤ M n ω)
    (hMbound : ∀ n k, k < n → ∀ ω, |D n k ω| ≤ M n ω)
    (hMint : ∀ n, Integrable (M n) P)
    (hMlim : Tendsto (fun n => ∫ ω, M n ω ∂P) atTop (𝓝 0))
    (hvar : TendstoInMeasure P
      (fun n ω => squareSum (fun j => D n j ω) n) atTop (fun _ => v)) :
    Tendsto (fun n => ∫ ω,
      Complex.exp ((t * ∑ j ∈ Finset.range n, D n j ω : ℝ) * Complex.I) ∂P)
      atTop (𝓝 (Complex.exp (-(t ^ 2 * v / 2 : ℝ)))) := by
  have hmeas : ∀ n k, Measurable (D n k) := fun n k =>
    (hadapt n k).mono (ℱ.le k) le_rfl
  have herror := tendsto_integral_stopped_error P D M t v hv hmeas hint
    hMnonneg hMbound hMint hMlim hvar
  have heq : ∀ n, (∫ ω, stoppedProduct (fun j => D n j ω) (v + 1) t n -
      phaseValue (fun j => D n j ω) t v n ∂P) =
      1 - ∫ ω, phaseValue (fun j => D n j ω) t v n ∂P := by
    intro n
    rw [integral_sub (integrable_stoppedProduct P (D n) (v + 1) t n (hmeas n) (hint n))
      (integrable_phaseValue P D t v n (hmeas n)),
      integral_stoppedProduct_eq_one P (D n) ℱ (v + 1) t (by linarith) n
        (hadapt n) (hint n) (hmds n) (hcent n)]
  have hphase : Tendsto (fun n => ∫ ω, phaseValue (fun j => D n j ω) t v n ∂P)
      atTop (𝓝 (1 : ℂ)) := by
    have hh := (tendsto_const_nhds (x := (1 : ℂ))).sub herror
    simpa only [heq, sub_sub_cancel, sub_zero] using hh
  let E : ℂ := Real.exp (t ^ 2 * v / 2)
  have hE : E ≠ 0 := by
    dsimp [E]
    exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (t ^ 2 * v / 2))
  have hfix : ∀ n, E⁻¹ * (∫ ω, phaseValue (fun j => D n j ω) t v n ∂P) =
      ∫ ω, Complex.exp ((t * ∑ j ∈ Finset.range n, D n j ω : ℝ) * Complex.I) ∂P := by
    intro n
    simp only [phaseValue, integral_const_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hE, one_mul]
  have hh := (tendsto_const_nhds (x := E⁻¹)).mul hphase
  simp only [hfix, mul_one] at hh
  simpa only [E, Complex.ofReal_exp, Complex.exp_neg] using hh

end IntegralConvergence

end MdsArray
end Component4

section Component5
open MeasureTheory
open scoped BigOperators

namespace MdsArray

lemma finiteMax_nonneg (n : ℕ) (D : ℕ → ℝ) :
    0 ≤ ⨆ k : Fin n, |D k.val| :=
  Real.iSup_nonneg (fun _ => abs_nonneg _)

lemma abs_le_finiteMax (n : ℕ) (D : ℕ → ℝ) (k : ℕ) (hk : k < n) :
    |D k| ≤ ⨆ j : Fin n, |D j.val| := by
  exact le_ciSup (Set.finite_range (fun j : Fin n => |D j.val|)).bddAbove ⟨k, hk⟩

lemma finiteMax_le_sum (n : ℕ) (D : ℕ → ℝ) :
    (⨆ k : Fin n, |D k.val|) ≤ ∑ k : Fin n, |D k.val| := by
  apply Real.iSup_le
  · intro k
    exact Finset.single_le_sum (fun j _ => abs_nonneg (D j.val)) (Finset.mem_univ k)
  · exact Finset.sum_nonneg (fun j _ => abs_nonneg (D j.val))

lemma measurable_finiteMax {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (D : ℕ → Ω → ℝ) (hmeas : ∀ k, Measurable (D k)) :
    Measurable (fun ω => ⨆ k : Fin n, |D k.val ω|) :=
  Measurable.iSup (fun k : Fin n => (hmeas k.val).abs)

lemma integrable_finiteMax {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (n : ℕ) (D : ℕ → Ω → ℝ)
    (hmeas : ∀ k, Measurable (D k)) (hint : ∀ k, Integrable (D k) P) :
    Integrable (fun ω => ⨆ k : Fin n, |D k.val ω|) P := by
  have hs : Integrable (fun ω => ∑ k : Fin n, |D k.val ω|) P :=
    integrable_finsetSum Finset.univ (fun k _ => (hint k.val).abs)
  apply hs.mono' (measurable_finiteMax n D hmeas).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (finiteMax_nonneg n (fun k => D k ω))]
  exact finiteMax_le_sum n (fun k => D k ω)

end MdsArray
end Component5

section Component6
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

set_option linter.unusedVariables false in
theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (D : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n k, Measurable (D n k))
    (hadapt : ∀ n k, Measurable[ℱ k] (D n k))
    (hint : ∀ n k, Integrable (D n k) P)
    (hmds : ∀ n k, P[D n (k + 1) | ℱ k] =ᵐ[P] 0)
    (hcent : ∀ n, ∫ ω, D n 0 ω ∂P = 0)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (hneg : Tendsto (fun n : ℕ => ∫ ω, ⨆ k : Fin n, |D n k.val ω| ∂P) atTop (𝓝 0))
    (hvar : TendstoInMeasure P
      (fun (n : ℕ) ω => ∑ k ∈ Finset.range n, D n k ω ^ 2) atTop (fun _ => σ ^ 2)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => ∑ k ∈ Finset.range n, D n k ω)
      atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 (σ ^ 2).toNNReal) := by
  have hs : ∀ n, Measurable (fun ω => ∑ k ∈ Finset.range n, D n k ω) :=
    fun n => Finset.measurable_sum _ (fun k _ => hmeas n k)
  refine { forall_aemeasurable := fun n => (hs n).aemeasurable, tendsto := ?_ }
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr fun t => ?_
  have hchar := MdsArray.tendsto_characteristic_integral P D
    (fun n ω => ⨆ k : Fin n, |D n k.val ω|) ℱ t (σ ^ 2) (sq_nonneg σ)
    hadapt hint hmds hcent
    (fun n ω => MdsArray.finiteMax_nonneg n (fun k => D n k ω))
    (fun n k hk ω => MdsArray.abs_le_finiteMax n (fun j => D n j ω) k hk)
    (fun n => MdsArray.integrable_finiteMax P n (D n) (hmeas n) (hint n)) hneg hvar
  have hmap : ∀ n, charFun (P.map (fun ω => ∑ k ∈ Finset.range n, D n k ω)) t =
      ∫ ω, Complex.exp ((t * ∑ k ∈ Finset.range n, D n k ω : ℝ) * Complex.I) ∂P := by
    intro n
    rw [charFun_apply_real, integral_map (hs n).aemeasurable (by fun_prop)]
    simp only [Complex.ofReal_mul]
  have hgauss : charFun (gaussianReal 0 (σ ^ 2).toNNReal) t =
      Complex.exp (-(t ^ 2 * σ ^ 2 / 2 : ℝ)) := by
    rw [charFun_gaussianReal]
    congr 1
    rw [Real.coe_toNNReal _ (sq_nonneg σ)]
    push_cast
    ring
  change Tendsto (fun n => charFun (P.map (fun ω => ∑ k ∈ Finset.range n, D n k ω)) t)
    atTop (𝓝 (charFun ((gaussianReal 0 (σ ^ 2).toNNReal).map id) t))
  simpa only [Measure.map_id, hmap, hgauss] using hchar
end Component6

