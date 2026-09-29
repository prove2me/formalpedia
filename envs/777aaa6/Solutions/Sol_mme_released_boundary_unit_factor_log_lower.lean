-- Prove2me | solution 1 for mme_released_boundary_unit_factor_log_lower
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T01:19:40.027319+00:00
-- url     : https://prove2.me/submissions/57c88daa-bb74-4203-b169-f9e010a931eb

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Theorems.Thm_mme_nat_multinomial_log_lower_mass_entropy
import Theorems.Thm_mme_released_boundary_unit_factor_mass_entropy_certificate
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm
open scoped Classical
set_option autoImplicit false

theorem solution :
    (6 * blocks 1 : ℝ) * ((450512205 : ℝ)/1000000000) ≤
      Real.log ((∏ c : Fin zCells,
        ((∑ s, zCountAt 1 c s).factorial / ∏ s, (zCountAt 1 c s).factorial) *
        5 ^ (∑ s, zCountAt 1 c s * Boundary.ones s) : ℕ) : ℝ) := by
  have hcert := mme_released_boundary_unit_factor_mass_entropy_certificate
  have hcard : (Fintype.card Word : ℝ) = 81 := by
    simp [Word, CompleteWord]
  have gen : ∀ {C : Type} [Fintype C] (z : C → Word → ℕ),
      ∑ c : C, (MME.RegionRate.massEntropy (fun s => (z c s : ℝ)) +
          ((∑ s, z c s * Boundary.ones s : ℕ) : ℝ) * Real.log 5) -
        ∑ c : C, 81 * Real.log (6 * (((∑ s, z c s : ℕ) : ℝ) + 1)) ≤
      Real.log ((∏ c : C,
        ((∑ s, z c s).factorial / ∏ s, (z c s).factorial) *
        5 ^ (∑ s, z c s * Boundary.ones s) : ℕ) : ℝ) := by
    intro C _ z
    have hpos : ∀ c : C, 0 < ((∑ s, z c s).factorial / ∏ s, (z c s).factorial) := by
      intro c
      have := Nat.multinomial_pos (Finset.univ : Finset Word) (fun s => z c s)
      simpa [Nat.multinomial] using this
    rw [Nat.cast_prod, Real.log_prod]
    · rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro c _
      have hl := mme_nat_multinomial_log_lower_mass_entropy (z c)
      rw [hcard] at hl
      have hM : (0:ℝ) < (((∑ s, z c s).factorial / ∏ s, (z c s).factorial : ℕ) : ℝ) := by
        exact_mod_cast hpos c
      rw [Nat.cast_mul, Real.log_mul hM.ne' (by positivity), Nat.cast_pow, Real.log_pow]
      push_cast at hl ⊢
      linarith
    · intro c _
      have := hpos c
      positivity
  have := gen (zCountAt 1)
  linarith
