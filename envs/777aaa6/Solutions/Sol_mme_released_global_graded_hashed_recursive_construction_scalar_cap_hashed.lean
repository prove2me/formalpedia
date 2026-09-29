-- Prove2me | solution 1 for mme_released_global_graded_hashed_recursive_construction_scalar_cap_hashed
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T23:04:43.645319+00:00
-- url     : https://prove2.me/submissions/8d8f1f90-baeb-4606-86f3-476549bca591

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Theorems.Thm_mme_released_global_graded_hashed_recursive_construction_scalar_cap_hashed_poly_inputs
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

/-- A polynomial number of inputs costs at most `k^2 ≤ 10^7 · blocks(k^2) / 10^7` in logarithm,
once `k` is at least the degree. -/
theorem poly_inputs_log_le (k C I : ℕ) (hCk : C ≤ k) (hI1 : 1 ≤ I) (hI : I ≤ (k + 1) ^ C) :
    Real.log (I : ℝ) ≤ (6 * blocks (k^2) : ℝ) * (1 / 10000000) := by
  have hIpos : (0 : ℝ) < I := by exact_mod_cast hI1
  have h1 : Real.log (I : ℝ) ≤ Real.log (((k : ℝ) + 1) ^ C) := by
    apply Real.log_le_log hIpos
    exact_mod_cast hI
  have h2 : Real.log (((k : ℝ) + 1) ^ C) = C * Real.log ((k : ℝ) + 1) := Real.log_pow _ _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h3 : Real.log ((k : ℝ) + 1) ≤ k := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < k + 1 by linarith)
    linarith
  have hC : (C : ℝ) ≤ k := by exact_mod_cast hCk
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hlog0 : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by linarith)
  have h4 : (C : ℝ) * Real.log ((k : ℝ) + 1) ≤ (k : ℝ) ^ 2 := by
    calc (C : ℝ) * Real.log ((k : ℝ) + 1) ≤ (k : ℝ) * k :=
          mul_le_mul hC h3 hlog0 hk0
      _ = (k : ℝ) ^ 2 := by ring
  have hb : (blocks (k^2) : ℝ) = (MoreAsymmetryExactSeed.denominator : ℝ) ^ 5 * (k : ℝ) ^ 2 := by
    unfold blocks; push_cast; ring
  have hD : (MoreAsymmetryExactSeed.denominator : ℝ) = 1000000000000 := by
    unfold MoreAsymmetryExactSeed.denominator; norm_num
  rw [hb, hD]
  have hk2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 := by positivity
  nlinarith

theorem solution :
    ∀ e : ℝ, 0 < e → e ≤ 1 →
      ∀ k0 : ℕ, ∃ k : ℕ, k0 ≤ k ∧
        ∀ (hk : 0 < k^2) (a : ∀ o : Fin 6, Reference o (k^2)),
          ∃ R : LogJointRecipeG (partSize (k^2) a 1) 3 (QPos (k^2) a (fun _ ↦ e)),
            1 ≤ R.inputs ∧
            1 ≤ R.a * R.b * R.c ∧
            (6 * blocks (k^2) : ℝ) * ((13223546 : ℝ)/10000000) +
              Real.log (R.inputs : ℝ) ≤ R.logOutputs ∧
            (6 * blocks (k^2) : ℝ) *
              (3 * ((209612367517 : ℝ)/100000000000) - 1/10000000) ≤
                (k^2 : ℝ) * Real.log ((∏ c : Fin zCells,
                  ((∑ s, zCountAt 1 c s).factorial / ∏ s, (zCountAt 1 c s).factorial) *
                  5 ^ (∑ s, zCountAt 1 c s * Boundary.ones s) : ℕ) : ℝ) +
                Real.log ((R.a * R.b * R.c : ℕ) : ℝ) := by
  intro e he0 he1
  obtain ⟨C, hC⟩ :=
    mme_released_global_graded_hashed_recursive_construction_scalar_cap_hashed_poly_inputs
      e he0 he1
  intro k0
  obtain ⟨k, hk0, H⟩ := hC (max k0 C)
  refine ⟨k, le_trans (le_max_left _ _) hk0, ?_⟩
  intro hk a
  obtain ⟨R, hin, hpoly, habc, hrate, hdim⟩ := H hk a
  refine ⟨R, hin, habc, ?_, hdim⟩
  have hlog := poly_inputs_log_le k C R.inputs (le_trans (le_max_right _ _) hk0) hin hpoly
  linarith
