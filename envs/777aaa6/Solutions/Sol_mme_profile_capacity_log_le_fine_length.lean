-- Prove2me | solution 1 for mme_profile_capacity_log_le_fine_length
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T14:02:17.841408+00:00
-- url     : https://prove2.me/submissions/ddec8f74-9c4d-4faf-8c11-d050bfc801e5

import Definitions.Def_mme_recursive_yz_CW_cells
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open scoped Classical
set_option autoImplicit false

/-- Every graded profile is a subset of the complete-word functions on its
positions, so three mode profiles have at most the unrestricted triple count. -/
private theorem mme_profile_capacity_le_unrestricted
    {P C : Type*} [Fintype P] (ell : ℕ) (cell : P → C)
    (shape : C → Fin 3 → ℕ) (mu : Fin 3 → C → CompleteWord ell → ℕ) :
    (∏ i : Fin 3, Nat.card (Block ell cell shape mu i)) ≤
      3 ^ (3 * (Fintype.card P * 2 ^ (ell - 1))) := by
  have h (i : Fin 3) : Nat.card (Block ell cell shape mu i) ≤
      (3 ^ (2 ^ (ell - 1))) ^ Fintype.card P := by
    have h := Nat.card_le_card_of_injective
      (fun f : Block ell cell shape mu i => f.val) Subtype.val_injective
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using h
  calc
    _ ≤ ∏ _ : Fin 3, (3 ^ (2 ^ (ell - 1))) ^ Fintype.card P :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => h i)
    _ = _ := by simp [← pow_mul, Nat.mul_comm]

/-- The logarithm of the repair capacity is bounded linearly in the number
of fine-word coordinates, independently of the specific profiles. -/
theorem solution
    {P C : Type*} [Fintype P] (ell : ℕ) (cell : P → C)
    (shape : C → Fin 3 → ℕ) (mu : Fin 3 → C → CompleteWord ell → ℕ) :
    Real.log (∏ i : Fin 3, Nat.card (Block ell cell shape mu i) : ℕ) ≤
      (3 * (Fintype.card P * 2 ^ (ell - 1)) : ℕ) * Real.log 3 := by
  let cap := ∏ i : Fin 3, Nat.card (Block ell cell shape mu i)
  by_cases hc : cap = 0
  · change Real.log (cap : ℝ) ≤ _
    rw [hc, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  · have hpos : (0 : ℝ) < cap := by exact_mod_cast Nat.pos_of_ne_zero hc
    have hbound : (cap : ℝ) ≤ (3 : ℝ) ^ (3 * (Fintype.card P * 2 ^ (ell - 1))) := by
      exact_mod_cast mme_profile_capacity_le_unrestricted ell cell shape mu
    have h := Real.log_le_log hpos hbound
    rw [Real.log_pow] at h
    exact h


#print axioms solution
