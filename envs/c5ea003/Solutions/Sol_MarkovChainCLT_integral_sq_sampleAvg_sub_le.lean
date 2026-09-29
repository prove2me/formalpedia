-- Prove2me | solution 1 for MarkovChainCLT.integral_sq_sampleAvg_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T23:31:25.321432+00:00
-- url     : https://prove2.me/submissions/64159fb6-f9d3-46e7-a611-5c0e1e70dcac

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Theorems.Thm_MarkovChainCLT_poissonEquation_of_bounded_of_uniformlyErgodic
import Theorems.Thm_MarkovChainCLT_integral_sq_sum_mds_le
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 1000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (huni : UniformlyErgodic P π) (lam : Measure X) [IsProbabilityMeasure lam]
    (φ : X → ℝ) (hφ : Measurable φ) (B : ℝ) (hB : ∀ x, |φ x| ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      ∫ ω, ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (ω (k + 1)) - ∫ x, φ x ∂π) ^ 2
          ∂(chainMeasure P lam) ≤ K / n := by
  classical
  obtain ⟨g, hgm, ⟨C, hgC⟩, hpois⟩ :=
    poissonEquation_of_bounded_of_uniformlyErgodic P π huni φ hφ B hB
  have hC0 : 0 ≤ C := by
    rcases isEmpty_or_nonempty X with hX | hX
    · have h1 : lam Set.univ = 1 := measure_univ
      rw [Set.univ_eq_empty_iff.mpr hX, measure_empty] at h1
      exact absurd h1 zero_ne_one
    · exact le_trans (abs_nonneg _) (hgC hX.some)
  set ν : Measure (ℕ → X) := chainMeasure P lam with hν
  set c₀ : ℝ := ∫ x, φ x ∂π with hc₀
  set Pg : X → ℝ := fun x => ∫ y, g y ∂(P x) with hPg
  have hPgm : Measurable Pg := (hgm.stronglyMeasurable.integral_kernel (κ := P)).measurable
  have hPgC : ∀ x, |Pg x| ≤ C := by
    intro x
    rw [hPg]
    refine le_trans abs_integral_le_integral_abs ?_
    have h1 : Integrable (fun y => |g y|) (P x) :=
      ⟨(continuous_abs.measurable.comp hgm).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ (fun z => by simpa using hgC z))⟩
    have h2 := integral_mono h1 (integrable_const C) (fun z => hgC z)
    simpa using h2
  set D : ℕ → (ℕ → X) → ℝ := fun k ω => g (ω (k + 1)) - Pg (ω k) with hD
  have hDm : ∀ k, Measurable (D k) :=
    fun k => (hgm.comp (measurable_pi_apply (k + 1))).sub (hPgm.comp (measurable_pi_apply k))
  -- the telescoping identity
  have hid : ∀ (n : ℕ), 1 ≤ n → ∀ ω : ℕ → X,
      ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (ω (k + 1)) - c₀)
        = (n : ℝ)⁻¹ * ((∑ k ∈ Finset.range n, D k ω) + (Pg (ω 0) - Pg (ω n))) := by
    intro n hn ω
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hstep : ∀ k, φ (ω (k + 1)) - c₀ = D k ω + (Pg (ω k) - Pg (ω (k + 1))) := by
      intro k
      have := hpois (ω (k + 1))
      simp only [hD, hPg] at *
      linarith
    have hsum : (∑ k ∈ Finset.range n, φ (ω (k + 1))) - (n : ℝ) * c₀
        = (∑ k ∈ Finset.range n, D k ω) + (Pg (ω 0) - Pg (ω n)) := by
      have h1 : (∑ k ∈ Finset.range n, φ (ω (k + 1))) - (n : ℝ) * c₀
          = ∑ k ∈ Finset.range n, (φ (ω (k + 1)) - c₀) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
        simp [mul_comm]
      rw [h1, Finset.sum_congr rfl (fun k _ => hstep k), Finset.sum_add_distrib,
        Finset.sum_range_sub' (fun i => Pg (ω i)) n]
    field_simp
    linarith [hsum]
  -- the pointwise bound
  have hpt : ∀ (n : ℕ), 1 ≤ n → ∀ ω : ℕ → X,
      ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (ω (k + 1)) - c₀) ^ 2
        ≤ 2 * ((n : ℝ)⁻¹) ^ 2 * (∑ k ∈ Finset.range n, D k ω) ^ 2
          + 2 * ((n : ℝ)⁻¹) ^ 2 * (2 * C) ^ 2 := by
    intro n hn ω
    rw [hid n hn ω]
    have hrem : |Pg (ω 0) - Pg (ω n)| ≤ 2 * C := by
      calc |Pg (ω 0) - Pg (ω n)| ≤ |Pg (ω 0)| + |Pg (ω n)| := abs_sub _ _
        _ ≤ 2 * C := by linarith [hPgC (ω 0), hPgC (ω n)]
    have hsq : (Pg (ω 0) - Pg (ω n)) ^ 2 ≤ (2 * C) ^ 2 := by
      nlinarith [abs_nonneg (Pg (ω 0) - Pg (ω n)), sq_abs (Pg (ω 0) - Pg (ω n))]
    have hab : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
      intro a b
      nlinarith [sq_nonneg (a - b)]
    have h1 := hab (∑ k ∈ Finset.range n, D k ω) (Pg (ω 0) - Pg (ω n))
    have hnn : (0 : ℝ) ≤ ((n : ℝ)⁻¹) ^ 2 := sq_nonneg _
    calc ((n : ℝ)⁻¹ * ((∑ k ∈ Finset.range n, D k ω) + (Pg (ω 0) - Pg (ω n)))) ^ 2
        = ((n : ℝ)⁻¹) ^ 2 * ((∑ k ∈ Finset.range n, D k ω) + (Pg (ω 0) - Pg (ω n))) ^ 2 := by
          ring
      _ ≤ ((n : ℝ)⁻¹) ^ 2 * (2 * (∑ k ∈ Finset.range n, D k ω) ^ 2
            + 2 * (Pg (ω 0) - Pg (ω n)) ^ 2) := by
          exact mul_le_mul_of_nonneg_left h1 hnn
      _ ≤ 2 * ((n : ℝ)⁻¹) ^ 2 * (∑ k ∈ Finset.range n, D k ω) ^ 2
            + 2 * ((n : ℝ)⁻¹) ^ 2 * (2 * C) ^ 2 := by
          nlinarith [hnn, hsq, sq_nonneg (∑ k ∈ Finset.range n, D k ω)]
  refine ⟨4 * (2 * C) ^ 2, by positivity, fun n hn => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- integrability
  have hsumint : Integrable (fun ω : ℕ → X => (∑ k ∈ Finset.range n, D k ω) ^ 2) ν := by
    refine ⟨((Finset.measurable_sum _ (fun k _ => hDm k)).pow_const 2).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := (n * (2 * C)) ^ 2) (ae_of_all _ (fun ω => ?_))⟩
    have hbd : |∑ k ∈ Finset.range n, D k ω| ≤ n * (2 * C) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have : ∀ k ∈ Finset.range n, |D k ω| ≤ 2 * C := by
        intro k _
        calc |D k ω| ≤ |g (ω (k + 1))| + |Pg (ω k)| := abs_sub _ _
          _ ≤ 2 * C := by linarith [hgC (ω (k + 1)), hPgC (ω k)]
      calc ∑ k ∈ Finset.range n, |D k ω| ≤ ∑ _k ∈ Finset.range n, (2 * C) :=
            Finset.sum_le_sum this
        _ = n * (2 * C) := by simp [Finset.sum_const, Finset.card_range]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (∑ k ∈ Finset.range n, D k ω),
      sq_abs (∑ k ∈ Finset.range n, D k ω), hbd,
      mul_nonneg (le_of_lt hnR) (by linarith : (0:ℝ) ≤ 2 * C)]
  have hlhsint : Integrable
      (fun ω : ℕ → X => ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (ω (k + 1)) - c₀) ^ 2) ν := by
    refine ⟨((((Finset.measurable_sum _
        (fun k _ => hφ.comp (measurable_pi_apply (k + 1)))).const_mul _).sub_const
        _).pow_const 2).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := (2 * B) ^ 2) (ae_of_all _ (fun ω => ?_))⟩
    have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (ω 0))
    have hbd : |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (ω (k + 1)) - c₀| ≤ 2 * B := by
      have h1 : |∑ k ∈ Finset.range n, φ (ω (k + 1))| ≤ n * B := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        calc ∑ k ∈ Finset.range n, |φ (ω (k + 1))|
            ≤ ∑ _k ∈ Finset.range n, B := Finset.sum_le_sum (fun k _ => hB _)
          _ = n * B := by simp [Finset.sum_const, Finset.card_range]
      have h2 : |c₀| ≤ B := by
        rw [hc₀]
        refine le_trans abs_integral_le_integral_abs ?_
        have hi : Integrable (fun y => |φ y|) π :=
          ⟨(continuous_abs.measurable.comp hφ).aestronglyMeasurable,
            HasFiniteIntegral.of_bounded (C := B)
              (ae_of_all _ (fun z => by simpa using hB z))⟩
        have := integral_mono hi (integrable_const B) (fun z => hB z)
        simpa using this
      have h3 : |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (ω (k + 1))| ≤ B := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹)]
        rw [inv_mul_le_iff₀ hnR]
        calc |∑ k ∈ Finset.range n, φ (ω (k + 1))| ≤ n * B := h1
          _ = n * B := rfl
      calc |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (ω (k + 1)) - c₀|
          ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (ω (k + 1))| + |c₀| := abs_sub _ _
        _ ≤ 2 * B := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (ω (k + 1)) - c₀),
      sq_abs ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (ω (k + 1)) - c₀), hbd, hB0]
  -- integrate the pointwise bound
  have hmain : ∫ ω, ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (ω (k + 1)) - c₀) ^ 2 ∂ν
      ≤ 2 * ((n : ℝ)⁻¹) ^ 2 * (∫ ω, (∑ k ∈ Finset.range n, D k ω) ^ 2 ∂ν)
        + 2 * ((n : ℝ)⁻¹) ^ 2 * (2 * C) ^ 2 := by
    have hrhsint : Integrable (fun ω : ℕ → X =>
        2 * ((n : ℝ)⁻¹) ^ 2 * (∑ k ∈ Finset.range n, D k ω) ^ 2
          + 2 * ((n : ℝ)⁻¹) ^ 2 * (2 * C) ^ 2) ν :=
      (hsumint.const_mul _).add (integrable_const _)
    have := integral_mono hlhsint hrhsint (fun ω => hpt n hn ω)
    rw [integral_add (hsumint.const_mul _) (integrable_const _), integral_const_mul,
      integral_const] at this
    simpa using this
  have hvar := integral_sq_sum_mds_le P lam g hgm C hgC n
  have hkey : ∫ ω, (∑ k ∈ Finset.range n, D k ω) ^ 2 ∂ν ≤ n * (2 * C) ^ 2 := hvar
  have hnn : (0 : ℝ) ≤ 2 * ((n : ℝ)⁻¹) ^ 2 := by positivity
  calc ∫ ω, ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (ω (k + 1)) - c₀) ^ 2 ∂ν
      ≤ 2 * ((n : ℝ)⁻¹) ^ 2 * (∫ ω, (∑ k ∈ Finset.range n, D k ω) ^ 2 ∂ν)
        + 2 * ((n : ℝ)⁻¹) ^ 2 * (2 * C) ^ 2 := hmain
    _ ≤ 2 * ((n : ℝ)⁻¹) ^ 2 * (n * (2 * C) ^ 2) + 2 * ((n : ℝ)⁻¹) ^ 2 * (2 * C) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hkey hnn
        linarith
    _ ≤ 4 * (2 * C) ^ 2 / n := by
        rw [div_eq_mul_inv]
        have hipos : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
        have hmul : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hnR)
        have hinv : (n : ℝ)⁻¹ ≤ 1 := by nlinarith [hmul, hipos, hn1]
        have hsq2 : ((n : ℝ)⁻¹) ^ 2 ≤ (n : ℝ)⁻¹ := by nlinarith [hipos, hinv]
        have hsq : (0:ℝ) ≤ (2 * C) ^ 2 := sq_nonneg _
        have e1 : 2 * ((n : ℝ)⁻¹) ^ 2 * ((n : ℝ) * (2 * C) ^ 2)
            = 2 * (n : ℝ)⁻¹ * (2 * C) ^ 2 := by
          field_simp
        rw [e1]
        nlinarith [mul_le_mul_of_nonneg_right hsq2 hsq]
