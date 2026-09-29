-- Prove2me | solution 1 for mme_released_level2_zero_half_mass_entropy_certificate
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T04:34:41.357342+00:00
-- url     : https://prove2.me/submissions/765a8563-760d-4916-af86-e637f201841d

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_regional_entropy_rate_data
import Theorems.Thm_mme_released_level2_zero_half_region0_mass_entropy_certificate
import Theorems.Thm_mme_released_level2_zero_half_region1_mass_entropy_certificate
import Theorems.Thm_mme_released_level2_zero_half_region2_mass_entropy_certificate
import Theorems.Thm_mme_released_level2_zero_half_region3_mass_entropy_certificate
import Theorems.Thm_mme_released_level2_zero_half_region4_mass_entropy_certificate
import Theorems.Thm_mme_released_level2_zero_half_region5_mass_entropy_certificate
open BigOperators MME MME.RecursiveYZ
set_option autoImplicit false

namespace C8Cert

/-- The summand of the certificate, for one region. -/
noncomputable def W (ρ : Fin 6)
    (c : {c : Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ) // ∃ j, (c.2.val j).val = 0}) : ℝ :=
  MME.RegionRate.massEntropy (fun w ↦ (RecStage.mu3 ρ
      (if (c.1.2.val 0).val = 0 then 1 else if (c.1.2.val 1).val = 0 then 2 else 0)
      c.1 w : ℝ)) +
    ((∑ w, RecStage.mu3 ρ
      (if (c.1.2.val 0).val = 0 then 1 else if (c.1.2.val 1).val = 0 then 2 else 0)
      c.1 w * Boundary.ones w : ℕ) : ℝ) * Real.log 5

def T : Fin 6 → ℕ := ![2090774427307984000000000000000000000000000000000000000000000,
  2089041627918284000000000000000000000000000000000000000000000,
  2085458999691735000000000000000000000000000000000000000000000,
  2082537758747372000000000000000000000000000000000000000000000,
  2101764658211037000000000000000000000000000000000000000000000,
  2096520761869059000000000000000000000000000000000000000000000]

theorem region (ρ : Fin 6) : ((T ρ : ℕ) : ℝ) ≤ ∑ c, W ρ c := by
  fin_cases ρ
  · exact mme_released_level2_zero_half_region0_mass_entropy_certificate
  · exact mme_released_level2_zero_half_region1_mass_entropy_certificate
  · exact mme_released_level2_zero_half_region2_mass_entropy_certificate
  · exact mme_released_level2_zero_half_region3_mass_entropy_certificate
  · exact mme_released_level2_zero_half_region4_mass_entropy_certificate
  · exact mme_released_level2_zero_half_region5_mass_entropy_certificate

theorem total : 12546098100 * 10 ^ 51 ≤ ∑ ρ : Fin 6, T ρ := by
  simp [T, Fin.sum_univ_six]

end C8Cert

open C8Cert in
theorem solution :
    ((12546098100 * 10 ^ 51 : ℕ) : ℝ) ≤
      ∑ z : (ρ : Fin 6) × {c : Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ) //
          ∃ j, (c.2.val j).val = 0},
        (MME.RegionRate.massEntropy (fun w ↦ (RecStage.mu3 z.1
            (if (z.2.1.2.val 0).val = 0 then 1 else if (z.2.1.2.val 1).val = 0 then 2 else 0)
            z.2.1 w : ℝ)) +
          ((∑ w, RecStage.mu3 z.1
            (if (z.2.1.2.val 0).val = 0 then 1 else if (z.2.1.2.val 1).val = 0 then 2 else 0)
            z.2.1 w * Boundary.ones w : ℕ) : ℝ) * Real.log 5) := by
  show _ ≤ ∑ z : (ρ : Fin 6) × {c : Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ) //
          ∃ j, (c.2.val j).val = 0}, W z.1 z.2
  rw [Fintype.sum_sigma]
  have h1 : ((∑ ρ : Fin 6, T ρ : ℕ) : ℝ) ≤ ∑ ρ : Fin 6, ∑ c, W ρ c := by
    push_cast
    exact Finset.sum_le_sum (fun ρ _ ↦ region ρ)
  have h2 : ((12546098100 * 10 ^ 51 : ℕ) : ℝ) ≤ ((∑ ρ : Fin 6, T ρ : ℕ) : ℝ) := by
    exact_mod_cast total
  exact h2.trans h1
