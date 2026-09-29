-- Prove2me | solution 1 for mme_stothers_general_outer_induced_family_multinomial_stationary
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-09T05:03:47.350618+00:00
-- url     : https://prove2.me/submissions/1a2bf808-36ed-4e91-93c5-3fd11e0e9589

import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_general_outer_hash_budget_stationary
import Theorems.Thm_mme_stothers_general_target_pruning_assembly

open MME BigOperators Filter

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth.GenInducedCount

private theorem row_sum (r : Fin 10) :
    (∑ j : Fin 9, genClassMarginalMultiplicity r j) = 3 * classMultiplicity r := by
  fin_cases r <;> decide

private theorem marginalCount_sum (base : Fin 10 → ℕ) (m : ℕ) :
    (∑ j : Fin 9, genMarginalCount base m j) = genOuterLength base m := by
  have hb : (∑ j : Fin 9, genMarginalBaseCount base j) = 3 * genProfileScale base := by
    simp only [genMarginalBaseCount, genProfileScale]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [← Finset.sum_mul, row_sum r]
    ring
  simp only [genMarginalCount, genOuterLength, ← Finset.sum_mul, hb]
  ring

private theorem multinomial_eq_factorial_ratio (base : Fin 10 → ℕ) (m : ℕ) :
    (Nat.multinomial Finset.univ
        (fun j : Fin 9 ↦ genMarginalBaseCount base j * m) : ℝ) =
      ((genOuterLength base m).factorial : ℝ) /
        ∏ j : Fin 9, ((genMarginalCount base m j).factorial : ℝ) := by
  let f : Fin 9 → ℕ := fun j ↦ genMarginalBaseCount base j * m
  let P : ℕ := ∏ j : Fin 9, (f j).factorial
  have hP : P ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ ↦ Nat.factorial_ne_zero _
  have hsum : ∑ j : Fin 9, f j = genOuterLength base m := by
    calc
      ∑ j : Fin 9, f j = ∑ j : Fin 9, genMarginalCount base m j := by
        apply Finset.sum_congr rfl
        intro j _hj
        simp only [f, genMarginalCount]
      _ = genOuterLength base m := marginalCount_sum base m
  have hspec := Nat.multinomial_spec Finset.univ f
  have hspec' :
      P * Nat.multinomial Finset.univ f = (genOuterLength base m).factorial := by
    simpa only [P, Finset.prod_filter, Finset.mem_univ, true_and, hsum] using hspec
  have hspecReal :
      (P : ℝ) * (Nat.multinomial Finset.univ f : ℝ) =
        ((genOuterLength base m).factorial : ℝ) := by
    exact_mod_cast hspec'
  have hratio :
      (Nat.multinomial Finset.univ f : ℝ) =
        ((genOuterLength base m).factorial : ℝ) / (P : ℝ) := by
    apply (eq_div_iff (by exact_mod_cast hP)).2
    simpa only [mul_comm] using hspecReal
  rw [hratio]
  simp only [P, Nat.cast_prod, f, genMarginalCount]

end MME.StothersFourth.GenInducedCount

theorem solution
    (base bstar : Fin 10 → ℕ)
    (hbase : ∀ r, 0 < base r) (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j)
    (hInN : MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar)) :
    ∀ᶠ m : ℕ in atTop,
      let N := MME.StothersFourth.genOuterLength base m
      ∃ F : Finset (MME.StothersFourth.GenExactOuterAddress base m),
        MME.StothersFourth.GenInducedModeDisjoint F ∧
        (Nat.multinomial Finset.univ
            (fun j : Fin 9 ↦ MME.StothersFourth.genMarginalBaseCount base j * m) : ℝ) *
          ((MME.StothersFourth.genHashTargetStarDegree base m : ℝ) /
            (((6 * (N + 1)) ^ 100 *
              MME.StothersFourth.genHashTargetStarDegree bstar m : ℕ) : ℝ)) *
          Real.exp (-1000000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤ (F.card : ℝ) := by
  filter_upwards [mme_stothers_general_outer_hash_budget_stationary base bstar
    hbase hbstar hsame hInN] with m hm
  obtain ⟨E, hclosed, hbudget⟩ := hm
  obtain ⟨F, hF, hprune⟩ :=
    mme_stothers_general_target_pruning_assembly base m E hclosed
  refine ⟨F, hF, ?_⟩
  rw [MME.StothersFourth.GenInducedCount.multinomial_eq_factorial_ratio]
  linarith
