-- Prove2me | solution 1 for mme_stothers_general_profile_outer_capacity_stationary
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-09T05:07:06.270676+00:00
-- url     : https://prove2.me/submissions/d21e1b77-d599-4743-8d0a-2932a2607e4e

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_general_profile_rate_below_marginal_multinomial
import Theorems.Thm_mme_stothers_general_outer_induced_family_multinomial_stationary

open MME BigOperators Filter

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.StothersFourth.GenCapacity

private theorem classValue_nonneg (tau : ℝ) (i : Fin 10) :
    0 ≤ classValue 6 tau i := by
  fin_cases i <;> simp [classValue, E, H, L] <;> positivity

private theorem marginalBaseCount_eq_Q (base : Fin 10 → ℕ) (j : Fin 9) :
    (genMarginalBaseCount base j : ℝ) = Q (fun i ↦ (base i : ℝ)) j := by
  fin_cases j <;>
    simp [genMarginalBaseCount, genClassMarginalMultiplicity, Q,
      Fin.sum_univ_succ] <;> ring

end MME.StothersFourth.GenCapacity

theorem solution
    (base bstar : Fin 10 → ℕ) (tau : ℝ)
    (hbase : ∀ r, 0 < base r) (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j)
    (hInN : MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let N := MME.StothersFourth.genOuterLength base m
        ∃ F : Finset (MME.StothersFourth.GenExactOuterAddress base m),
          MME.StothersFourth.GenInducedModeDisjoint F ∧
          (MME.StothersFourth.globalRate 6 tau
                (MME.StothersFourth.genProfileB base)
                (MME.StothersFourth.genProfileB base)) ^ N *
              ((MME.StothersFourth.genHashTargetStarDegree base m : ℝ) /
                (((6 * (N + 1)) ^ 100 *
                  MME.StothersFourth.genHashTargetStarDegree bstar m : ℕ) : ℝ)) *
              Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
            (F.card : ℝ) *
              (∏ r : Fin 10,
                (MME.StothersFourth.classValue 6 tau r) ^
                  (MME.StothersFourth.classMultiplicity r *
                    MME.StothersFourth.genProfileCount base m r)) := by
  obtain ⟨Crate, hCrate, hrate⟩ :=
    mme_stothers_general_profile_rate_below_marginal_multinomial tau
      (MME.StothersFourth.genProfileB base) base
      (MME.StothersFourth.genMarginalBaseCount base)
      (MME.StothersFourth.genProfileScale base) hbase rfl
      (fun i => rfl)
      (MME.StothersFourth.GenCapacity.marginalBaseCount_eq_Q base)
  refine ⟨Crate + 1000000, by linarith, ?_⟩
  filter_upwards [hrate,
    mme_stothers_general_outer_induced_family_multinomial_stationary base bstar
      hbase hbstar hsame hInN] with m hrateM hfamilyM
  obtain ⟨F, hF, hcount⟩ := hfamilyM
  refine ⟨F, hF, ?_⟩
  set N := MME.StothersFourth.genOuterLength base m with hN
  set s : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ)) with hs
  set M : ℝ :=
    ((Nat.multinomial Finset.univ
      (fun j : Fin 9 ↦ MME.StothersFourth.genMarginalBaseCount base j * m) : ℕ) : ℝ) with hM
  set R : ℝ :=
    (MME.StothersFourth.genHashTargetStarDegree base m : ℝ) /
      (((6 * (N + 1)) ^ 100 *
        MME.StothersFourth.genHashTargetStarDegree bstar m : ℕ) : ℝ) with hR
  set Gpow : ℝ :=
    (MME.StothersFourth.globalRate 6 tau
      (MME.StothersFourth.genProfileB base)
      (MME.StothersFourth.genProfileB base)) ^ N with hG
  set I : ℝ :=
    ∏ r : Fin 10,
      (MME.StothersFourth.classValue 6 tau r) ^
        (MME.StothersFourth.classMultiplicity r *
          MME.StothersFourth.genProfileCount base m r) with hI
  have hInonneg : 0 ≤ I :=
    Finset.prod_nonneg fun r _ ↦
      pow_nonneg (MME.StothersFourth.GenCapacity.classValue_nonneg tau r) _
  have hRnonneg : 0 ≤ R :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hrate' : Gpow * Real.exp (-Crate * s) ≤ M * I := by
    have hNeq : 3 * MME.StothersFourth.genProfileScale base * m = N := by
      rw [hN]; simp only [MME.StothersFourth.genOuterLength]; ring
    rw [hNeq] at hrateM
    exact hrateM
  have hcount' : M * R * Real.exp (-1000000 * s) ≤ (F.card : ℝ) := hcount
  calc
    Gpow * R * Real.exp (-(Crate + 1000000) * s)
        = (Gpow * Real.exp (-Crate * s)) * (R * Real.exp (-1000000 * s)) := by
          rw [show -(Crate + 1000000) * s = (-Crate * s) + (-1000000 * s) by ring,
            Real.exp_add]
          ring
    _ ≤ (M * I) * (R * Real.exp (-1000000 * s)) := by
          have hpos : 0 ≤ R * Real.exp (-1000000 * s) :=
            mul_nonneg hRnonneg (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right hrate' hpos
    _ = (M * R * Real.exp (-1000000 * s)) * I := by ring
    _ ≤ (F.card : ℝ) * I := mul_le_mul_of_nonneg_right hcount' hInonneg
