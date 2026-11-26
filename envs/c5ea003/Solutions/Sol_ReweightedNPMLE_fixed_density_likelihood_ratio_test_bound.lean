-- Prove2me | solution 1 for ReweightedNPMLE.fixed_density_likelihood_ratio_test_bound
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:06:38.606803+00:00
-- url     : https://prove2.me/submissions/9bb9c0b1-2572-4c18-9add-9bbd106a340c

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Hellinger
import Theorems.Thm_ReweightedNPMLE_density_mul_exp_half_log_ratio
import Theorems.Thm_ReweightedNPMLE_fixed_likelihood_ratio_test_bound_real
import Theorems.Thm_ReweightedNPMLE_hellingerSq_eq_integrals
import Theorems.Thm_ReweightedNPMLE_integrable_exp_half_log_ratio_withDensity
import Theorems.Thm_ReweightedNPMLE_product_exp_half_log_ratio_integral

-- Inline helpers preserved from ReweightedNPMLE.Hellinger.
section
/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

namespace ReweightedNPMLE















theorem hellingerSq_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ) : 0 ≤ hellingerSq μ p q := by
  apply integral_nonneg
  intro x
  exact sq_nonneg _



















/-- For probability densities, affinity equals `1 - H²/2`. -/
theorem affinity_eq_one_sub_half_hellingerSq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ)
    (haint : Integrable (fun x ↦ Real.sqrt (p x * q x)) μ)
    (hp_one : ∫ x, p x ∂μ = 1) (hq_one : ∫ x, q x ∂μ = 1) :
    hellingerAffinity μ p q = 1 - hellingerSq μ p q / 2 := by
  have h := hellingerSq_eq_integrals μ p q hp hq hpint hqint haint
  rw [hp_one, hq_one] at h
  linarith

theorem hellingerAffinity_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ) : 0 ≤ hellingerAffinity μ p q := by
  apply integral_nonneg
  intro x
  exact Real.sqrt_nonneg _

/-- Under the paper's convention, squared Hellinger distance between densities is at most two. -/
theorem hellingerSq_le_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ)
    (haint : Integrable (fun x ↦ Real.sqrt (p x * q x)) μ)
    (hp_one : ∫ x, p x ∂μ = 1) (hq_one : ∫ x, q x ∂μ = 1) :
    hellingerSq μ p q ≤ 2 := by
  have ha := hellingerAffinity_nonneg μ p q
  rw [affinity_eq_one_sub_half_hellingerSq μ p q hp hq hpint hqint haint hp_one hq_one] at ha
  linarith





/-- Exponentiating half of a finite log-likelihood ratio turns its sum into
the product of the coordinatewise square-root likelihood ratios. -/
theorem exp_half_sum_log_ratio_eq_prod {Ω : Type*} {n : ℕ}
    (p q : Ω → ℝ) (x : Fin n → Ω) :
    Real.exp ((∑ i, Real.log (p (x i) / q (x i))) / 2) =
      ∏ i, Real.exp (Real.log (p (x i) / q (x i)) / 2) := by
  rw [div_eq_mul_inv, Finset.sum_mul, Real.exp_sum]
  simp only [div_eq_mul_inv]



/-- Under the probability law with density `q`, the one-observation
square-root likelihood-ratio expectation is exactly the Hellinger affinity. -/
theorem integral_exp_half_log_ratio_withDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hqmeas : Measurable q) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x) :
    ∫ x, Real.exp (Real.log (p x / q x) / 2)
        ∂μ.withDensity (fun x ↦ ENNReal.ofReal (q x)) =
      hellingerAffinity μ p q := by
  rw [integral_withDensity_eq_integral_toReal_smul]
  · change (∫ x, (ENNReal.ofReal (q x)).toReal *
        Real.exp (Real.log (p x / q x) / 2) ∂μ) = _
    simp_rw [ENNReal.toReal_ofReal (hq _).le,
      density_mul_exp_half_log_ratio (hp _) (hq _)]
    rfl
  · exact hqmeas.ennreal_ofReal
  · exact Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top



/-- The exact product likelihood-ratio identity used in the finite-net test. -/
theorem product_sqrt_likelihood_ratio_identity
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hqmeas : Measurable q) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    [SigmaFinite (μ.withDensity fun x ↦ ENNReal.ofReal (q x))] :
    ∫ x : Fin n → Ω,
        Real.exp ((∑ i, Real.log (p (x i) / q (x i))) / 2)
        ∂Measure.pi (fun _ : Fin n ↦
          μ.withDensity (fun y ↦ ENNReal.ofReal (q y))) =
      (hellingerAffinity μ p q) ^ n := by
  rw [product_exp_half_log_ratio_integral]
  rw [integral_exp_half_log_ratio_withDensity μ p q hqmeas hp hq]

/-- Probability-density specialization in exactly the form displayed in the
manuscript: the product expectation is `(1 - H²/2)ⁿ`. -/
theorem product_sqrt_likelihood_ratio_eq_one_sub_half_hellingerSq
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hqmeas : Measurable q)
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ)
    (haint : Integrable (fun x ↦ Real.sqrt (p x * q x)) μ)
    (hp_one : ∫ x, p x ∂μ = 1) (hq_one : ∫ x, q x ∂μ = 1)
    [SigmaFinite (μ.withDensity fun x ↦ ENNReal.ofReal (q x))] :
    ∫ x : Fin n → Ω,
        Real.exp ((∑ i, Real.log (p (x i) / q (x i))) / 2)
        ∂Measure.pi (fun _ : Fin n ↦
          μ.withDensity (fun y ↦ ENNReal.ofReal (q y))) =
      (1 - hellingerSq μ p q / 2) ^ n := by
  rw [product_sqrt_likelihood_ratio_identity μ p q hqmeas hp hq]
  rw [affinity_eq_one_sub_half_hellingerSq μ p q
    (fun x ↦ (hp x).le) (fun x ↦ (hq x).le) hpint hqint haint hp_one hq_one]

end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.FiniteNet.
section
/-!
# Finite-net likelihood testing

This file isolates the probability-theoretic union-bound step in the proof of
the paper's uniform near-MLE theorem.  The analytic construction of a
Gaussian-mixture net and the fixed-density likelihood-ratio estimate enter as
explicit hypotheses; the passage from those pointwise estimates to one event
which controls every candidate is proved here.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ReweightedNPMLE

/-- The elementary affinity-power bound used in the fixed-net test. -/
theorem affinity_pow_le_exp_neg {h : ℝ} (hh₀ : 0 ≤ h) (hh₂ : h ≤ 2) (n : ℕ) :
    (1 - h / 2) ^ n ≤ Real.exp (-(n : ℝ) * h / 2) := by
  have hbase : 0 ≤ 1 - h / 2 := by linarith
  calc
    (1 - h / 2) ^ n ≤ (Real.exp (-h / 2)) ^ n := by
      convert pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg (h / 2)) n using 1 <;>
        ring
    _ = Real.exp (-(n : ℝ) * h / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring























end ReweightedNPMLE
end

/-!
# Finite-net likelihood testing

This file isolates the probability-theoretic union-bound step in the proof of
the paper's uniform near-MLE theorem.  The analytic construction of a
Gaussian-mixture net and the fixed-density likelihood-ratio estimate enter as
explicit hypotheses; the passage from those pointwise estimates to one event
which controls every candidate is proved here.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
/--
The fixed-density likelihood-ratio test with all analytic premises discharged.
Samples are drawn independently from the probability density `q` with
respect to `μ`.  The right-hand side is the exponential Hellinger bound used
before taking the finite-net union bound.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hqmeas : Measurable q) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ)
    (haint : Integrable (fun x ↦ Real.sqrt (p x * q x)) μ)
    (hp_one : ∫ x, p x ∂μ = 1) (hq_one : ∫ x, q x ∂μ = 1) :
    (Measure.pi (fun _ : Fin n ↦
      μ.withDensity (fun y ↦ ENNReal.ofReal (q y)))).real
        {x | -2 ≤ ∑ i, Real.log (p (x i) / q (x i))} ≤
      Real.exp (1 - (n : ℝ) * hellingerSq μ p q / 2) := by
  let ν : Measure Ω := μ.withDensity fun y ↦ ENNReal.ofReal (q y)
  letI : IsProbabilityMeasure ν := IsProbabilityMeasure.mk (by
    dsimp [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hqint
        (Filter.Eventually.of_forall fun x ↦ (hq x).le), hq_one]
    norm_num)
  let logLR : (Fin n → Ω) → ℝ :=
    fun x ↦ ∑ i, Real.log (p (x i) / q (x i))
  have hbase : Integrable
      (fun y ↦ Real.exp (Real.log (p y / q y) / 2)) ν := by
    exact integrable_exp_half_log_ratio_withDensity μ p q hqmeas hp hq haint
  have hprod : Integrable
      (fun x : Fin n → Ω ↦
        ∏ i, Real.exp (Real.log (p (x i) / q (x i)) / 2))
      (Measure.pi fun _ : Fin n ↦ ν) :=
    Integrable.fintype_prod (fun _ ↦ hbase)
  have hint : Integrable (fun x ↦ Real.exp (logLR x / 2))
      (Measure.pi fun _ : Fin n ↦ ν) := by
    apply hprod.congr
    exact Filter.Eventually.of_forall fun x ↦
      (exp_half_sum_log_ratio_eq_prod p q x).symm
  have hh₀ : 0 ≤ hellingerSq μ p q := hellingerSq_nonneg μ p q
  have hh₂ : hellingerSq μ p q ≤ 2 :=
    hellingerSq_le_two μ p q (fun x ↦ (hp x).le) (fun x ↦ (hq x).le)
      hpint hqint haint hp_one hq_one
  have hexpect :
      ∫ x, Real.exp (logLR x / 2) ∂Measure.pi (fun _ : Fin n ↦ ν) ≤
        Real.exp (-(n : ℝ) * hellingerSq μ p q / 2) := by
    calc
      _ = (1 - hellingerSq μ p q / 2) ^ n := by
        exact product_sqrt_likelihood_ratio_eq_one_sub_half_hellingerSq
          μ p q hqmeas hp hq hpint hqint haint hp_one hq_one
      _ ≤ _ := affinity_pow_le_exp_neg hh₀ hh₂ n
  exact fixed_likelihood_ratio_test_bound_real
    (Measure.pi fun _ : Fin n ↦ ν) logLR n (hellingerSq μ p q) hint hexpect
