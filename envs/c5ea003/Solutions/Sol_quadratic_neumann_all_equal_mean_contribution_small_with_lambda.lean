-- Prove2me | solution 1 for quadratic_neumann_all_equal_mean_contribution_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-23T03:59:53.588791+00:00
-- url     : https://prove2.me/submissions/eb1def5e-dad6-4e72-87dd-520b3d3125c7

import Theorems.Thm_quadratic_neumann_all_equal_base_spectral_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_all_equal_mean_as_scaled_base_matrix
import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped Classical BigOperators

set_option maxHeartbeats 1000000

namespace Bot5_92

/-- Spectral norm is absolutely homogeneous. -/
theorem spectralNorm_smul {n1 n2 : Nat} (c : ℝ) (X : RealMatrix n1 n2) :
    spectralNorm (c • X) = |c| * spectralNorm X := by
  unfold spectralNorm
  rw [show (Matrix.toEuclideanLin (c • X))
        = c • (Matrix.toEuclideanLin X) from by
        ext v; simp [map_smul]]
  rw [show (LinearMap.toContinuousLinearMap (c • Matrix.toEuclideanLin X))
        = c • (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)) from by
        ext v; simp]
  rw [norm_smul]
  simp [Real.norm_eq_abs]

theorem spectralNorm_nonneg {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    0 ≤ spectralNorm X := by
  unfold spectralNorm; exact norm_nonneg _

/-- The factored mean coefficient |(p⁻¹)²(1-3p+2p²)| ≤ (p⁻¹)² for 0 ≤ p ≤ 1. -/
theorem factor_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |(p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2)| ≤ (p⁻¹) ^ 2 := by
  rw [abs_mul]
  have h1 : |(p⁻¹) ^ 2| = (p⁻¹) ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
  rw [h1]
  have h2 : |1 - 3 * p + 2 * p ^ 2| ≤ 1 := by
    rw [show 1 - 3 * p + 2 * p ^ 2 = (1 - p) * (1 - 2 * p) by ring]
    rw [abs_mul]
    have ha : |1 - p| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
    have hb : |1 - 2 * p| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    calc |1 - p| * |1 - 2 * p| ≤ 1 * 1 := by
            apply mul_le_mul ha hb (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  nlinarith [sq_nonneg (p⁻¹), h2, abs_nonneg ((1:ℝ) - 3 * p + 2 * p ^ 2)]

/-- `β · log(max) ≥ 1` when `β > 2` and `max ≥ 2`. -/
theorem beta_log_ge_one (β : ℝ) (hβ : 2 < β) (x : ℝ) (hx : 2 ≤ x) :
    1 ≤ β * Real.log x := by
  have hlog2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- 2 * log 2 = log 4 ≥ 1  (since 4 ≥ e)
  have h4 : (1:ℝ) ≤ 2 * Real.log 2 := by
    rw [show (2:ℝ) * Real.log 2 = Real.log 4 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring]
    rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_three
    linarith
  calc (1:ℝ) ≤ 2 * Real.log 2 := h4
    _ ≤ β * Real.log x := by
        apply mul_le_mul (le_of_lt hβ) hlog2 (le_of_lt hlog2pos) (by linarith)

/-- The core scale-absorption: under the density hypothesis and `max ≥ 2`,
`(max)² μ₀² r² / m² ≤ lam^(-3/2)`. -/
theorem core_absorption (β lam : ℝ) (hβ : 2 < β) (hlam : 1 ≤ lam)
    (n₁ n₂ r m : ℕ) (μ₀ : ℝ) (hμ0 : 1 ≤ μ₀) (hrR : (1:ℝ) ≤ (r:ℝ))
    (hmaxge2 : (2:ℝ) ≤ (↑(max n₁ n₂) : ℝ))
    (hlogpos : 0 < Real.log (↑(max n₁ n₂)))
    (hmR : (0:ℝ) < (m:ℝ))
    (hdens : (m : ℝ) ≥
      lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
        (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
          (β * Real.log (↑(max n₁ n₂)))) :
    (↑(max n₁ n₂) : ℝ) ^ 2 * μ₀ ^ 2 * (r:ℝ) ^ 2 / (m:ℝ) ^ 2 ≤
      Real.rpow lam (-((3 : ℝ) / 2)) := by
  set X : ℝ := (↑(max n₁ n₂) : ℝ) with hX
  set L : ℝ := Real.log X with hL
  have hXpos : 0 < X := by linarith
  have hμ0pos : 0 < μ₀ := by linarith
  have hrpos : 0 < (r:ℝ) := by linarith
  have hlampos : 0 < lam := by linarith
  set D : ℝ := lam * Real.rpow μ₀ ((4 : ℝ) / 3) * X * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
      (β * L) with hD
  have hμpow : 0 < Real.rpow μ₀ ((4:ℝ)/3) := Real.rpow_pos_of_pos hμ0pos _
  have hrpow : 0 < Real.rpow (r:ℝ) ((4:ℝ)/3) := Real.rpow_pos_of_pos hrpos _
  have hβpos : 0 < β := by linarith
  have hDpos : 0 < D := by rw [hD]; positivity
  -- m ≥ D ⇒ m² ≥ D²
  have hm2 : D ^ 2 ≤ (m:ℝ) ^ 2 := by
    apply pow_le_pow_left₀ (le_of_lt hDpos) hdens
  -- It suffices: X² μ₀² r² ≤ lam^(-3/2) * D²
  rw [div_le_iff₀ (by positivity)]
  -- Goal: X² μ₀² r² ≤ lam^(-3/2) * m²
  have key : X ^ 2 * μ₀ ^ 2 * (r:ℝ) ^ 2 ≤ Real.rpow lam (-((3:ℝ)/2)) * D ^ 2 := by
    -- D² = lam² (μ₀^{4/3})² X² (r^{4/3})² (β L)²
    have hDsq : D ^ 2 = lam ^ 2 * (Real.rpow μ₀ ((4:ℝ)/3)) ^ 2 * X ^ 2 *
        (Real.rpow (r:ℝ) ((4:ℝ)/3)) ^ 2 * (β * L) ^ 2 := by
      rw [hD]; ring
    rw [hDsq]
    -- lam^{-3/2} * lam² = lam^{1/2}
    have hlamcombine : Real.rpow lam (-((3:ℝ)/2)) * lam ^ 2 = Real.rpow lam ((1:ℝ)/2) := by
      rw [show lam ^ 2 = Real.rpow lam (2:ℝ) from (Real.rpow_two lam).symm,
          show Real.rpow lam (-((3:ℝ)/2)) * Real.rpow lam (2:ℝ)
            = Real.rpow lam (-((3:ℝ)/2) + (2:ℝ)) from (Real.rpow_add hlampos _ _).symm]
      norm_num
    -- (μ₀^{4/3})² = μ₀^{8/3} ;  μ₀^{8/3} = μ₀² · μ₀^{2/3}
    have hμsq : (Real.rpow μ₀ ((4:ℝ)/3)) ^ 2 = μ₀ ^ 2 * Real.rpow μ₀ ((2:ℝ)/3) := by
      have e1 : (Real.rpow μ₀ ((4:ℝ)/3)) ^ 2 = Real.rpow μ₀ ((8:ℝ)/3) := by
        rw [pow_two,
            show Real.rpow μ₀ ((4:ℝ)/3) * Real.rpow μ₀ ((4:ℝ)/3)
              = Real.rpow μ₀ ((4:ℝ)/3 + (4:ℝ)/3) from (Real.rpow_add hμ0pos _ _).symm]
        norm_num
      have e2 : μ₀ ^ 2 * Real.rpow μ₀ ((2:ℝ)/3) = Real.rpow μ₀ ((8:ℝ)/3) := by
        rw [show (μ₀ ^ 2) = Real.rpow μ₀ (2:ℝ) from (Real.rpow_two μ₀).symm]
        rw [show Real.rpow μ₀ (2:ℝ) * Real.rpow μ₀ ((2:ℝ)/3)
              = Real.rpow μ₀ ((2:ℝ) + (2:ℝ)/3) from (Real.rpow_add hμ0pos _ _).symm]
        norm_num
      rw [e1, e2]
    have hrsq : (Real.rpow (r:ℝ) ((4:ℝ)/3)) ^ 2 = (r:ℝ) ^ 2 * Real.rpow (r:ℝ) ((2:ℝ)/3) := by
      have e1 : (Real.rpow (r:ℝ) ((4:ℝ)/3)) ^ 2 = Real.rpow (r:ℝ) ((8:ℝ)/3) := by
        rw [pow_two,
            show Real.rpow (r:ℝ) ((4:ℝ)/3) * Real.rpow (r:ℝ) ((4:ℝ)/3)
              = Real.rpow (r:ℝ) ((4:ℝ)/3 + (4:ℝ)/3) from (Real.rpow_add hrpos _ _).symm]
        norm_num
      have e2 : (r:ℝ) ^ 2 * Real.rpow (r:ℝ) ((2:ℝ)/3) = Real.rpow (r:ℝ) ((8:ℝ)/3) := by
        rw [show ((r:ℝ) ^ 2) = Real.rpow (r:ℝ) (2:ℝ) from (Real.rpow_two (r:ℝ)).symm]
        rw [show Real.rpow (r:ℝ) (2:ℝ) * Real.rpow (r:ℝ) ((2:ℝ)/3)
              = Real.rpow (r:ℝ) ((2:ℝ) + (2:ℝ)/3) from (Real.rpow_add hrpos _ _).symm]
        norm_num
      rw [e1, e2]
    rw [hμsq, hrsq]
    -- Now RHS = lam^{-3/2} * (lam² μ₀² μ₀^{2/3} X² r² r^{2/3} (βL)²)
    -- factor: = (lam^{-3/2} lam²) · μ₀^{2/3} · r^{2/3} · (βL)² · (X² μ₀² r²)
    have hfactors : Real.rpow lam (-((3:ℝ)/2)) *
        (lam ^ 2 * (μ₀ ^ 2 * Real.rpow μ₀ ((2:ℝ)/3)) * X ^ 2 *
          ((r:ℝ) ^ 2 * Real.rpow (r:ℝ) ((2:ℝ)/3)) * (β * L) ^ 2)
        = (Real.rpow lam ((1:ℝ)/2) * Real.rpow μ₀ ((2:ℝ)/3) *
            Real.rpow (r:ℝ) ((2:ℝ)/3) * (β * L) ^ 2) * (X ^ 2 * μ₀ ^ 2 * (r:ℝ) ^ 2) := by
      rw [← hlamcombine]; ring
    rw [hfactors]
    -- need: X²μ₀²r² ≤ M · (X²μ₀²r²) where M ≥ 1
    have hbase_nn : 0 ≤ X ^ 2 * μ₀ ^ 2 * (r:ℝ) ^ 2 := by positivity
    have hM_ge1 : 1 ≤ Real.rpow lam ((1:ℝ)/2) * Real.rpow μ₀ ((2:ℝ)/3) *
        Real.rpow (r:ℝ) ((2:ℝ)/3) * (β * L) ^ 2 := by
      have hlamhalf : 1 ≤ Real.rpow lam ((1:ℝ)/2) :=
        Real.one_le_rpow hlam (by norm_num)
      have hμhalf : 1 ≤ Real.rpow μ₀ ((2:ℝ)/3) :=
        Real.one_le_rpow hμ0 (by norm_num)
      have hrhalf : 1 ≤ Real.rpow (r:ℝ) ((2:ℝ)/3) :=
        Real.one_le_rpow hrR (by norm_num)
      have hbL : 1 ≤ β * L := beta_log_ge_one β hβ X hmaxge2
      have hbLsq : 1 ≤ (β * L) ^ 2 := by nlinarith [hbL]
      calc (1:ℝ) = 1 * 1 * 1 * 1 := by ring
        _ ≤ Real.rpow lam ((1:ℝ)/2) * Real.rpow μ₀ ((2:ℝ)/3) *
              Real.rpow (r:ℝ) ((2:ℝ)/3) * (β * L) ^ 2 := by
            apply mul_le_mul
            apply mul_le_mul
            apply mul_le_mul hlamhalf hμhalf (by norm_num) (le_trans (by norm_num) hlamhalf)
            exact hrhalf
            · norm_num
            · positivity
            · exact hbLsq
            · norm_num
            · positivity
    calc X ^ 2 * μ₀ ^ 2 * (r:ℝ) ^ 2
        = 1 * (X ^ 2 * μ₀ ^ 2 * (r:ℝ) ^ 2) := by ring
      _ ≤ (Real.rpow lam ((1:ℝ)/2) * Real.rpow μ₀ ((2:ℝ)/3) *
            Real.rpow (r:ℝ) ((2:ℝ)/3) * (β * L) ^ 2) * (X ^ 2 * μ₀ ^ 2 * (r:ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_right hM_ge1 hbase_nn
  -- combine: X²μ₀²r² ≤ lam^{-3/2} D² ≤ lam^{-3/2} m²
  calc X ^ 2 * μ₀ ^ 2 * (r:ℝ) ^ 2 ≤ Real.rpow lam (-((3:ℝ)/2)) * D ^ 2 := key
    _ ≤ Real.rpow lam (-((3:ℝ)/2)) * (m:ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hm2 (Real.rpow_nonneg (le_of_lt hlampos) _)

end Bot5_92

open Bot5_92

theorem solution :
    ∃ Cmean : ℝ, 0 < Cmean ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        spectralNorm
            (quadraticNeumannAllEqualMeanContribution S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cmean * Real.rpow lam (-((3 : ℝ) / 2)) := by
  obtain ⟨Cbase, hCbase_pos, hCbase⟩ :=
    quadratic_neumann_all_equal_base_spectral_norm_bound_min_dim
  refine ⟨Cbase, hCbase_pos, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn1 hn2 hr hm hμ0 hμ1 hA0 hA1 hdens
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
  -- basic positivity facts
  have hn1R : (0:ℝ) < (n₁:ℝ) := by exact_mod_cast hn1
  have hn2R : (0:ℝ) < (n₂:ℝ) := by exact_mod_cast hn2
  have hrR : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hmaxR : (0:ℝ) < (↑(max n₁ n₂) : ℝ) := by
    have : 0 < max n₁ n₂ := lt_of_lt_of_le hn1 (le_max_left _ _)
    exact_mod_cast this
  have hminR : (0:ℝ) < (↑(min n₁ n₂) : ℝ) := by
    have : 0 < min n₁ n₂ := lt_min hn1 hn2
    exact_mod_cast this
  -- p bounds 0 ≤ p ≤ 1
  have hmle : (m:ℝ) ≤ (n₁:ℝ) * (n₂:ℝ) := by exact_mod_cast hm
  have hp0 : 0 ≤ p := by rw [hp_def]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp_def, div_le_one (by positivity)]; exact hmle
  -- mean = scalar • base
  have hscaled := quadratic_neumann_all_equal_mean_as_scaled_base_matrix S p
  -- base spectral bound (min form)
  have hbase := hCbase n₁ n₂ r M μ₀ S hn1 hn2 hr hμ0 hA0
  -- spectralNorm(mean) = |scalar| * spectralNorm(base)
  rw [hscaled, spectralNorm_smul]
  set sc : ℝ := (p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2) with hsc_def
  -- spectralNorm(base) ≤ Cbase * (μ₀ r / min)^2
  set B : ℝ := Cbase * ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2) with hB_def
  have hBnn : 0 ≤ B := by rw [hB_def]; positivity
  have hRHSnn : 0 ≤ Cbase * Real.rpow lam (-((3 : ℝ) / 2)) := by
    apply mul_nonneg (le_of_lt hCbase_pos) (Real.rpow_nonneg (by linarith) _)
  -- The lam^(-3/2) RHS is nonneg; spectralNorm(base) ≥ 0
  have hsn_nn := spectralNorm_nonneg (quadraticNeumannAllEqualBaseMatrix S)
  -- Case split on max n₁ n₂ = 1 (the degenerate 1×1 corner) vs ≥ 2.
  rcases Nat.lt_or_ge (max n₁ n₂) 2 with hmax_small | hmax_big
  · -- max ≤ 1, so max = 1, n₁ = n₂ = 1, m ≤ 1.
    have hn1e : n₁ = 1 := by
      have := le_max_left n₁ n₂; omega
    have hn2e : n₂ = 1 := by
      have := le_max_right n₁ n₂; omega
    subst hn1e; subst hn2e
    -- n₁ n₂ = 1, m ≤ 1
    have : m ≤ 1 := by simpa using hm
    interval_cases m
    · -- m = 0 ⇒ p = 0 ⇒ sc = 0
      have hp00 : p = 0 := by rw [hp_def]; norm_num
      rw [show sc = 0 by rw [hsc_def, hp00]; norm_num]
      rw [abs_zero, zero_mul]; exact hRHSnn
    · -- m = 1 ⇒ p = 1 ⇒ (1-3p+2p²)=0 ⇒ sc = 0
      have hp11 : p = 1 := by rw [hp_def]; norm_num
      rw [show sc = 0 by rw [hsc_def, hp11]; norm_num]
      rw [abs_zero, zero_mul]; exact hRHSnn
  · -- max n₁ n₂ ≥ 2
    have hmaxge2 : (2:ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by exact_mod_cast hmax_big
    -- |sc| ≤ (p⁻¹)^2
    have hsc_le : |sc| ≤ (p⁻¹) ^ 2 := factor_le p hp0 hp1
    have step1 : |sc| * spectralNorm (quadraticNeumannAllEqualBaseMatrix S)
        ≤ (p⁻¹) ^ 2 * B := by
      calc |sc| * spectralNorm (quadraticNeumannAllEqualBaseMatrix S)
          ≤ (p⁻¹) ^ 2 * spectralNorm (quadraticNeumannAllEqualBaseMatrix S) := by
            apply mul_le_mul_of_nonneg_right hsc_le hsn_nn
        _ ≤ (p⁻¹) ^ 2 * B := by
            apply mul_le_mul_of_nonneg_left hbase (by positivity)
    refine le_trans step1 ?_
    -- m > 0 here since m ≥ density > 0 (max≥2 ⇒ density > 0). Establish m > 0.
    have hlogpos : 0 < Real.log (↑(max n₁ n₂)) := by
      apply Real.log_pos; exact_mod_cast (by omega : 1 < max n₁ n₂)
    have hDpos : 0 < lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
          (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
            (β * Real.log (↑(max n₁ n₂))) := by
      have h1 : (0:ℝ) < Real.rpow μ₀ ((4:ℝ)/3) := Real.rpow_pos_of_pos (by linarith) _
      have h2 : (0:ℝ) < Real.rpow (r:ℝ) ((4:ℝ)/3) := Real.rpow_pos_of_pos (by linarith) _
      have : (0:ℝ) < β := by linarith
      positivity
    have hmR : (0:ℝ) < (m:ℝ) := lt_of_lt_of_le hDpos hdens
    have hpinv : p⁻¹ = ((n₁:ℝ) * (n₂:ℝ)) / (m:ℝ) := by rw [hp_def, inv_div]
    have hminmax : (↑(min n₁ n₂) : ℝ) * (↑(max n₁ n₂) : ℝ) = (n₁:ℝ) * (n₂:ℝ) := by
      rw [← Nat.cast_mul]; exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (min_mul_max n₁ n₂)
    have hminmax2 : (↑(min n₁ n₂) : ℝ) ^ 2 * (↑(max n₁ n₂) : ℝ) ^ 2
        = (n₁:ℝ) ^ 2 * (n₂:ℝ) ^ 2 := by
      rw [show (↑(min n₁ n₂) : ℝ) ^ 2 * (↑(max n₁ n₂) : ℝ) ^ 2
            = ((↑(min n₁ n₂) : ℝ) * (↑(max n₁ n₂) : ℝ)) ^ 2 by ring, hminmax]; ring
    have hcollapse : (p⁻¹) ^ 2 * ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2)
        = (↑(max n₁ n₂) : ℝ) ^ 2 * μ₀ ^ 2 * (r:ℝ) ^ 2 / (m:ℝ) ^ 2 := by
      rw [hpinv]
      rw [div_pow, div_pow, div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
      rw [show ((n₁:ℝ) * (n₂:ℝ)) ^ 2 * (μ₀ * (r:ℝ)) ^ 2 = (μ₀ ^ 2 * (r:ℝ) ^ 2) * ((n₁:ℝ) ^ 2 * (n₂:ℝ) ^ 2) by ring,
          ← hminmax2]
      ring
    rw [hB_def, show (p⁻¹) ^ 2 * (Cbase * ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2))
          = Cbase * ((p⁻¹) ^ 2 * ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2)) by ring,
        hcollapse]
    apply mul_le_mul_of_nonneg_left ?_ (le_of_lt hCbase_pos)
    -- CORE: (max)^2 μ₀² r² / m² ≤ lam^(-3/2)
    exact core_absorption β lam hβ hlam n₁ n₂ r m μ₀ hμ0 hrR hmaxge2 hlogpos
      hmR hdens
