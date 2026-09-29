-- Prove2me | solution 1 for mme_stothers_fixed_profile_outer_capacity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:09:46.765035+00:00
-- url     : https://prove2.me/submissions/65682871-c673-4d6b-aff9-e4aba70835d1

import Theorems.Thm_mme_stothers_fixed_profile_rate_below_marginal_multinomial
import Theorems.Thm_mme_stothers_fixed_outer_induced_family_multinomial

open MME BigOperators Filter

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth.FixedOuterCapacityReduction

private theorem fixedClassValue_nonneg (tau : ℝ) (i : Fin 10) :
    0 ≤ classValue 6 tau i := by
  fin_cases i <;>
    simp [classValue, E, H, L] <;> positivity

end MME.StothersFourth.FixedOuterCapacityReduction

theorem solution
    (tau : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in Filter.atTop,
        ∃ F : Finset (MME.StothersFourth.FixedExactOuterAddress m),
          MME.StothersFourth.FixedInducedModeDisjoint F ∧
          (MME.StothersFourth.globalRate 6 tau
                MME.StothersFourth.fixedProfileB
                MME.StothersFourth.fixedProfileB) ^
                (MME.StothersFourth.fixedOuterLength m) *
              Real.exp
                (-C * Real.sqrt
                  (((MME.StothersFourth.fixedOuterLength m + 1 : ℕ) : ℝ))) ≤
            (F.card : ℝ) *
              (∏ r : Fin 10,
                (MME.StothersFourth.classValue 6 tau r) ^
                  (MME.StothersFourth.classMultiplicity r *
                    MME.StothersFourth.fixedProfileCount m r)) := by
  obtain ⟨Crate, hCrate, hrate⟩ :=
    mme_stothers_fixed_profile_rate_below_marginal_multinomial tau
  obtain ⟨Cfamily, hCfamily, hfamily⟩ :=
    mme_stothers_fixed_outer_induced_family_multinomial
  refine ⟨Crate + Cfamily, add_nonneg hCrate hCfamily, ?_⟩
  filter_upwards [hrate, hfamily] with m hrateM hfamilyM
  obtain ⟨F, hF, hcount⟩ := hfamilyM
  refine ⟨F, hF, ?_⟩
  let s : ℝ := Real.sqrt
    (((MME.StothersFourth.fixedOuterLength m + 1 : ℕ) : ℝ))
  let Gpow : ℝ :=
    (MME.StothersFourth.globalRate 6 tau
      MME.StothersFourth.fixedProfileB
      MME.StothersFourth.fixedProfileB) ^
        MME.StothersFourth.fixedOuterLength m
  let M : ℝ :=
    Nat.multinomial Finset.univ
      (fun j : Fin 9 ↦
        MME.StothersFourth.fixedMarginalBaseCount j * m)
  let I : ℝ :=
    ∏ r : Fin 10,
      (MME.StothersFourth.classValue 6 tau r) ^
        (MME.StothersFourth.classMultiplicity r *
          MME.StothersFourth.fixedProfileCount m r)
  have hI : 0 ≤ I := by
    dsimp only [I]
    exact Finset.prod_nonneg fun r _ ↦
      pow_nonneg
        (MME.StothersFourth.FixedOuterCapacityReduction.fixedClassValue_nonneg
          tau r) _
  have hrateM' :
      Gpow * Real.exp (-Crate * s) ≤ M * I := by
    simpa only [Gpow, M, I, s] using hrateM
  have hcount' :
      M * Real.exp (-Cfamily * s) ≤ (F.card : ℝ) := by
    simpa only [M, s] using hcount
  calc
    Gpow * Real.exp (-(Crate + Cfamily) * s) =
        (Gpow * Real.exp (-Crate * s)) *
          Real.exp (-Cfamily * s) := by
      rw [show -(Crate + Cfamily) * s =
          (-Crate * s) + (-Cfamily * s) by ring,
        Real.exp_add]
      ring
    _ ≤ (M * I) * Real.exp (-Cfamily * s) :=
      mul_le_mul_of_nonneg_right hrateM' (Real.exp_pos _).le
    _ = (M * Real.exp (-Cfamily * s)) * I := by ring
    _ ≤ (F.card : ℝ) * I :=
      mul_le_mul_of_nonneg_right hcount' hI

