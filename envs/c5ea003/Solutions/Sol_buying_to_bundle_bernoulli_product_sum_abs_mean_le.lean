-- Prove2me | solution 1 for buying_to_bundle_bernoulli_product_sum_abs_mean_le
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-07-04T01:52:37.068479+00:00
-- url     : https://prove2.me/submissions/5432ddef-1e6c-4df6-b671-83d6dcf31410

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic
import Theorems.Thm_finite_integral_abs_sub_integral_le_sqrt_variance

open MeasureTheory
open scoped BigOperators

namespace BuyingToBundle

private lemma bernoulli_toReal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    let pp : NNReal := ⟨p, hp0⟩
    let hpp : pp ≤ 1 := by
      change (pp : ℝ) ≤ (1 : ℝ)
      change p ≤ 1
      exact hp1
    ((PMF.bernoulli pp hpp b).toReal : ℝ) = if b then p else 1 - p := by
  intro pp hpp
  cases b
  · simp [PMF.bernoulli_apply]
    rw [← ENNReal.coe_one, ← ENNReal.coe_sub, ENNReal.coe_toReal]
    rw [NNReal.coe_sub hpp]
    change (1 : ℝ) - p = 1 - p
    rfl
  · simp [PMF.bernoulli_apply]
    change p = p
    rfl

private lemma bernoulli_toMeasure_singleton_toReal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    let pp : NNReal := ⟨p, hp0⟩
    let hpp : pp ≤ 1 := by
      change (pp : ℝ) ≤ (1 : ℝ)
      change p ≤ 1
      exact hp1
    ((((PMF.bernoulli pp hpp).toMeasure) {b}).toReal : ℝ) =
      if b then p else 1 - p := by
  intro pp hpp
  rw [PMF.toMeasure_apply_singleton _ b (MeasurableSet.singleton b)]
  exact bernoulli_toReal p hp0 hp1 b

private lemma bernoulli_product_singleton_toReal
    {N : ℕ} (p : Fin N → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (I : Fin N → Bool) :
    let pp : Fin N → NNReal := fun i => ⟨p i, hp0 i⟩
    let hpp : ∀ i, pp i ≤ 1 := by
      intro i
      change (pp i : ℝ) ≤ (1 : ℝ)
      change p i ≤ 1
      exact hp1 i
    (((Measure.pi fun i => (PMF.bernoulli (pp i) (hpp i)).toMeasure) {I}).toReal : ℝ) =
      ∏ i, if I i then p i else 1 - p i := by
  classical
  intro pp hpp
  let νi : Fin N → Measure Bool := fun i => (PMF.bernoulli (pp i) (hpp i)).toMeasure
  have hsingle :
      ({I} : Set (Fin N → Bool)) = Set.univ.pi (fun i : Fin N => ({I i} : Set Bool)) := by
    ext J
    simp [Set.pi_def, funext_iff]
  rw [hsingle]
  rw [Measure.pi_pi]
  change (((∏ i, νi i ({I i} : Set Bool)) : ENNReal).toReal : ℝ) =
    ∏ i, if I i then p i else 1 - p i
  rw [ENNReal.toReal_prod]
  · exact Finset.prod_congr rfl fun i _ => by
      simpa [νi, pp] using bernoulli_toMeasure_singleton_toReal (p i) (hp0 i) (hp1 i) (I i)

private lemma bernoulli_product_integral_abs_eq_sum
    {N : ℕ} (p a : Fin N → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    let pp : Fin N → NNReal := fun i => ⟨p i, hp0 i⟩
    let hpp : ∀ i, pp i ≤ 1 := by
      intro i
      change (pp i : ℝ) ≤ (1 : ℝ)
      change p i ≤ 1
      exact hp1 i
    (∫ I : Fin N → Bool,
        |(∑ i, if I i then a i else 0) - ∑ i, p i * a i|
        ∂(Measure.pi fun i => (PMF.bernoulli (pp i) (hpp i)).toMeasure)) =
      ∑ I : Fin N → Bool,
        (∏ i, if I i then p i else 1 - p i) *
          |(∑ i, if I i then a i else 0) - ∑ i, p i * a i| := by
  classical
  intro pp hpp
  let ν : Measure (Fin N → Bool) :=
    Measure.pi fun i => (PMF.bernoulli (pp i) (hpp i)).toMeasure
  rw [MeasureTheory.integral_fintype (μ := ν) (f := fun I : Fin N → Bool =>
      |(∑ i, if I i then a i else 0) - ∑ i, p i * a i|) MeasureTheory.Integrable.of_finite]
  simp only [ν, smul_eq_mul]
  exact Finset.sum_congr rfl fun I _ => by
    change (((Measure.pi fun i => (PMF.bernoulli (pp i) (hpp i)).toMeasure) {I}).toReal : ℝ) *
        |(∑ i, if I i then a i else 0) - ∑ i, p i * a i| =
      (∏ i, if I i then p i else 1 - p i) *
        |(∑ i, if I i then a i else 0) - ∑ i, p i * a i|
    rw [show (((Measure.pi fun i => (PMF.bernoulli (pp i) (hpp i)).toMeasure) {I}).toReal : ℝ) =
        ∏ i, if I i then p i else 1 - p i by
      simpa [pp] using bernoulli_product_singleton_toReal p hp0 hp1 I]

private lemma bernoulli_integral_bool
    (p a : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let pp : NNReal := ⟨p, hp0⟩
    let hpp : pp ≤ 1 := by
      change (pp : ℝ) ≤ (1 : ℝ)
      change p ≤ 1
      exact hp1
    (∫ b : Bool, (if b then a else 0) ∂(PMF.bernoulli pp hpp).toMeasure) = p * a := by
  intro pp hpp
  rw [PMF.integral_eq_sum]
  rw [Fintype.sum_bool]
  have htrue : ((PMF.bernoulli pp hpp) true).toReal • (if true then a else 0 : ℝ) =
      (pp : ℝ) * a := by
    simp [PMF.bernoulli_apply, smul_eq_mul]
  have hfalse : ((PMF.bernoulli pp hpp) false).toReal •
      (if false then a else 0 : ℝ) = 0 := by
    simp
  rw [htrue, hfalse, add_zero]
  change (pp : ℝ) * a = p * a
  change p * a = p * a
  rfl

private lemma bernoulli_product_integral_sum_eq
    {N : ℕ} (p a : Fin N → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    let pp : Fin N → NNReal := fun i => ⟨p i, hp0 i⟩
    let hpp : ∀ i, pp i ≤ 1 := by
      intro i
      change (pp i : ℝ) ≤ (1 : ℝ)
      change p i ≤ 1
      exact hp1 i
    let ν : Measure (Fin N → Bool) := Measure.pi fun i => (PMF.bernoulli (pp i) (hpp i)).toMeasure
    (∫ I : Fin N → Bool, ∑ i, if I i then a i else 0 ∂ν) = ∑ i, p i * a i := by
  intro pp hpp ν
  have hcoord : ∀ i : Fin N,
      (∫ I : Fin N → Bool, (if I i then a i else 0) ∂ν) = p i * a i := by
    intro i
    let Xi : Bool → ℝ := fun b => if b then a i else 0
    have hmap : Measure.map (fun I : Fin N → Bool => I i) ν =
        (PMF.bernoulli (pp i) (hpp i)).toMeasure := by
      simpa [ν] using
        (measurePreserving_eval (fun j => (PMF.bernoulli (pp j) (hpp j)).toMeasure) i).map_eq
    have hsm : AEStronglyMeasurable Xi
        (Measure.map (fun I : Fin N → Bool => I i) ν) :=
      AEStronglyMeasurable.of_discrete
    have hmapint :
        (∫ b, Xi b ∂Measure.map (fun I : Fin N → Bool => I i) ν) =
          ∫ I : Fin N → Bool, Xi (I i) ∂ν := by
      exact integral_map (measurable_pi_apply i).aemeasurable hsm
    rw [hmap] at hmapint
    rw [← hmapint]
    simpa [Xi, pp] using bernoulli_integral_bool (p i) (a i) (hp0 i) (hp1 i)
  rw [MeasureTheory.integral_finset_sum Finset.univ]
  · exact Finset.sum_congr rfl fun i _ => hcoord i
  · intro i hi
    exact MeasureTheory.Integrable.of_finite

private lemma finite_memLp_two {Ω : Type*} [MeasurableSpace Ω] [Finite Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) :
    MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
  exact ⟨AEStronglyMeasurable.of_discrete, eLpNorm_lt_top_of_finite⟩

private lemma bernoulli_product_variance_sum_le
    {N : ℕ} {μH : ℝ} (p a : Fin N → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ha0 : ∀ i, 0 ≤ a i) (haH : ∀ i, a i ≤ μH) (hμH0 : 0 ≤ μH) :
    let pp : Fin N → NNReal := fun i => ⟨p i, hp0 i⟩
    let hpp : ∀ i, pp i ≤ 1 := by
      intro i
      change (pp i : ℝ) ≤ (1 : ℝ)
      change p i ≤ 1
      exact hp1 i
    let ν : Measure (Fin N → Bool) := Measure.pi fun i => (PMF.bernoulli (pp i) (hpp i)).toMeasure
    ProbabilityTheory.variance
        (fun I : Fin N → Bool => ∑ i, if I i then a i else 0) ν ≤
      (N : ℝ) * μH ^ 2 := by
  classical
  intro pp hpp ν
  let Xi : (i : Fin N) → Bool → ℝ := fun i b => if b then a i else 0
  have hvarsum :
      ProbabilityTheory.variance
          (fun I : Fin N → Bool => ∑ i, if I i then a i else 0) ν =
        ∑ i, ProbabilityTheory.variance (Xi i)
          ((PMF.bernoulli (pp i) (hpp i)).toMeasure) := by
    have hvarsum0 :
        ProbabilityTheory.variance
            (∑ i, fun I : Fin N → Bool => Xi i (I i)) ν =
          ∑ i, ProbabilityTheory.variance (Xi i)
            ((PMF.bernoulli (pp i) (hpp i)).toMeasure) := by
      simpa [ν] using
        (ProbabilityTheory.variance_sum_pi
          (μ := fun i => (PMF.bernoulli (pp i) (hpp i)).toMeasure)
          (X := Xi)
          (fun i => by
            convert finite_memLp_two ((PMF.bernoulli (pp i) (hpp i)).toMeasure) (Xi i)
            norm_num))
    have hfun :
        (∑ i, fun I : Fin N → Bool => Xi i (I i)) =
          fun I : Fin N → Bool => ∑ i, if I i then a i else 0 := by
      funext I
      simp [Xi]
    rw [← hfun]
    exact hvarsum0
  have hcoord_le : ∀ i : Fin N,
      ProbabilityTheory.variance (Xi i) ((PMF.bernoulli (pp i) (hpp i)).toMeasure) ≤
        μH ^ 2 := by
    intro i
    let μi : Measure Bool := (PMF.bernoulli (pp i) (hpp i)).toMeasure
    haveI : IsProbabilityMeasure μi := by
      dsimp [μi]
      infer_instance
    have hvarle :
        ProbabilityTheory.variance (Xi i) μi ≤ ∫ b, (Xi i b) ^ 2 ∂μi := by
      simpa [Pi.pow_apply] using
        (ProbabilityTheory.variance_le_expectation_sq
          (μ := μi) (X := Xi i) (AEStronglyMeasurable.of_discrete))
    have hsquare_le_ae : (fun b => (Xi i b) ^ 2) ≤ᵐ[μi] fun _ => μH ^ 2 := by
      filter_upwards with b
      cases b <;> simp [Xi]
      · exact sq_nonneg μH
      · nlinarith [ha0 i, haH i, hμH0]
    have hintle : (∫ b, (Xi i b) ^ 2 ∂μi) ≤ ∫ b : Bool, μH ^ 2 ∂μi := by
      exact integral_mono_ae MeasureTheory.Integrable.of_finite (integrable_const _) hsquare_le_ae
    have hconst : (∫ b : Bool, μH ^ 2 ∂μi) = μH ^ 2 := by
      rw [integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
    exact hvarle.trans (hintle.trans_eq hconst)
  calc
    ProbabilityTheory.variance
        (fun I : Fin N → Bool => ∑ i, if I i then a i else 0) ν
        = ∑ i, ProbabilityTheory.variance (Xi i)
          ((PMF.bernoulli (pp i) (hpp i)).toMeasure) := hvarsum
    _ ≤ ∑ i : Fin N, μH ^ 2 := Finset.sum_le_sum fun i _ => hcoord_le i
    _ = (N : ℝ) * μH ^ 2 := by simp

/-
Paper source: "Buying to Bundle: Optimal Sourcing from Monopolistic Sellers",
Appendix C.2, proof of Theorem 4.6, p. 35, Eq. (5).

This is the conditional finite-product Bernoulli part of Eq. (5).  For fixed
qualities `a_i` bounded between `0` and `muH`, and independent inclusion
probabilities `p_i ∈ [0,1]`, the explicit finite mixture over inclusion
patterns has expected absolute fluctuation at most `muH * sqrt N`.
-/
theorem buying_to_bundle_bernoulli_product_sum_abs_mean_le
    {N : ℕ} {μH : ℝ} (hμH0 : 0 ≤ μH)
    (p a : Fin N → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ha0 : ∀ i, 0 ≤ a i) (haH : ∀ i, a i ≤ μH) :
    (∑ I : Fin N → Bool,
        (∏ i, if I i then p i else 1 - p i) *
          |(∑ i, if I i then a i else 0) - ∑ i, p i * a i|) ≤
      μH * Real.sqrt N := by
  classical
  let pp : Fin N → NNReal := fun i => ⟨p i, hp0 i⟩
  let hpp : ∀ i, pp i ≤ 1 := by
    intro i
    change (pp i : ℝ) ≤ (1 : ℝ)
    change p i ≤ 1
    exact hp1 i
  let ν : Measure (Fin N → Bool) := Measure.pi fun i => (PMF.bernoulli (pp i) (hpp i)).toMeasure
  let Y : (Fin N → Bool) → ℝ := fun I => ∑ i, if I i then a i else 0
  have hsum_eq_int :
      (∫ I : Fin N → Bool, |Y I - ∑ i, p i * a i| ∂ν) =
        ∑ I : Fin N → Bool,
          (∏ i, if I i then p i else 1 - p i) *
            |(∑ i, if I i then a i else 0) - ∑ i, p i * a i| := by
    simpa [ν, Y, pp] using bernoulli_product_integral_abs_eq_sum p a hp0 hp1
  have hmean : (∫ I : Fin N → Bool, Y I ∂ν) = ∑ i, p i * a i := by
    simpa [ν, Y, pp] using bernoulli_product_integral_sum_eq p a hp0 hp1
  have hdev :
      (∫ I : Fin N → Bool, |Y I - ∑ i, p i * a i| ∂ν) ≤
        Real.sqrt (ProbabilityTheory.variance Y ν) := by
    have h := finite_integral_abs_sub_integral_le_sqrt_variance ν Y
    rw [hmean] at h
    exact h
  have hvar :
      ProbabilityTheory.variance Y ν ≤ (N : ℝ) * μH ^ 2 := by
    simpa [ν, Y, pp] using
      bernoulli_product_variance_sum_le (μH := μH) p a hp0 hp1 ha0 haH hμH0
  have hsqrt :
      Real.sqrt ((N : ℝ) * μH ^ 2) = μH * Real.sqrt N := by
    calc
      Real.sqrt ((N : ℝ) * μH ^ 2)
          = Real.sqrt (N : ℝ) * Real.sqrt (μH ^ 2) := by
            rw [Real.sqrt_mul (Nat.cast_nonneg N) (μH ^ 2)]
      _ = Real.sqrt (N : ℝ) * μH := by
            rw [Real.sqrt_sq hμH0]
      _ = μH * Real.sqrt N := by ring
  rw [← hsum_eq_int]
  exact hdev.trans ((Real.sqrt_le_sqrt hvar).trans_eq hsqrt)

end BuyingToBundle

theorem solution
    {N : ℕ} {μH : ℝ} (hμH0 : 0 ≤ μH)
    (p a : Fin N → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ha0 : ∀ i, 0 ≤ a i) (haH : ∀ i, a i ≤ μH) :
    (∑ I : Fin N → Bool,
        (∏ i, if I i then p i else 1 - p i) *
          |(∑ i, if I i then a i else 0) - ∑ i, p i * a i|) ≤
      μH * Real.sqrt N := by
  exact BuyingToBundle.buying_to_bundle_bernoulli_product_sum_abs_mean_le
    hμH0 p a hp0 hp1 ha0 haH
