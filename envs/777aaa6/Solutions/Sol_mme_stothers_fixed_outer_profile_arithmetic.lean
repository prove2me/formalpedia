-- Prove2me | solution 1 for mme_stothers_fixed_outer_profile_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T18:52:22.567127+00:00
-- url     : https://prove2.me/submissions/a158474b-1638-4380-ba4b-795b54df11ea

import Definitions.Def_mme_stothers_fixed_outer_profile
import Mathlib.Tactic

open MME BigOperators
open MME.StothersFourth

set_option autoImplicit false
set_option maxRecDepth 100000

theorem solution :
    (∀ i : Fin 10, 0 < fixedProfileBaseCount i) ∧
    (∑ i : Fin 10,
        classMultiplicity i * fixedProfileBaseCount i = fixedProfileScale) ∧
    (∀ r : Fin 10, ∀ s : Fin 3, ∀ j : Fin 9,
      ((fixedClassOrbit r).filter (fun σ ↦ σ s = j)).card =
        fixedClassMarginalMultiplicity r j) ∧
    (∀ j : Fin 9,
      fixedMarginalBaseCount j =
        ∑ r : Fin 10,
          fixedClassMarginalMultiplicity r j * fixedProfileBaseCount r) ∧
    (∑ j : Fin 9, fixedMarginalBaseCount j = 3 * fixedProfileScale) ∧
    InN fixedProfileB := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [fixedProfileBaseCount]
  · norm_num [classMultiplicity, fixedProfileBaseCount, fixedProfileScale,
      Fin.sum_univ_succ]
  · have h : ∀ r : Fin 10, ∀ s : Fin 3, ∀ j : Fin 9,
        ((fixedClassOrbit r).filter (fun σ ↦ σ s = j)).card =
          fixedClassMarginalMultiplicity r j := by
      decide
    exact h
  · intro j
    fin_cases j <;>
      norm_num [fixedMarginalBaseCount, fixedClassMarginalMultiplicity,
        fixedProfileBaseCount, Fin.sum_univ_succ]
  · norm_num [fixedMarginalBaseCount, fixedProfileScale, Fin.sum_univ_succ]
  · refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro i
        dsimp only [fixedProfileB]
        positivity
      · norm_num [fixedProfileB, fixedProfileBaseCount, fixedProfileScale,
          classMultiplicity, Fin.sum_univ_succ]
        rfl
    · change
        ((73075 : ℝ) / 97942072) *
            ((13720000 : ℝ) / 97942072) ^ (2 : ℕ) =
          ((3626000 : ℝ) / 97942072) *
            ((98000 : ℝ) / 97942072) *
              ((38710000 : ℝ) / 97942072)
      norm_num
    · change
        ((1023050 : ℝ) / 97942072) *
            ((13720000 : ℝ) / 97942072) *
              ((21560000 : ℝ) / 97942072) =
          ((3626000 : ℝ) / 97942072) *
            ((2156000 : ℝ) / 97942072) *
              ((38710000 : ℝ) / 97942072)
      norm_num
