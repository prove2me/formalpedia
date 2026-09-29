-- Prove2me | solution 1 for mme_dwz_table2_fifteen_multiplicity_common_power_product_of_local_strict_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T07:14:43.259339+00:00
-- url     : https://prove2.me/submissions/4d711c6f-93df-46ad-9d52-98f196c8e363

import Mathlib.Tactic
import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_dwz_square_componentBase_pos
import Theorems.Thm_mme_finite_HasTauValueAtLeast_common_power_multiplicity_product_below

open MME BigOperators MME.DWZSquare

set_option autoImplicit false
set_option warningAsError true

universe u

theorem solution
    {K : Type u} [Field K]
    (component : Fin 15 → TensorObj K 3)
    (multiplicity : Fin 15 → ℕ) (tau : ℝ)
    (target : Fin 15 → ℝ)
    (htarget : ∀ s, 0 ≤ target s)
    (hstrict : ∀ s, target s < componentBase tau s)
    (hlocal : ∀ (s : Fin 15) (W : ℝ),
      0 ≤ W → W < componentBase tau s →
      HasTauValueAtLeast (component s) tau W) :
    ∃ E : ℕ, 0 < E ∧
      ∀ r : ℕ,
        ∃ (q : ℕ) (A B C : Fin q → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (C j)))
            ((TensorObj.kronFin 15
              (fun s ↦ (component s).kronPow (multiplicity s))).kronPow
                (r * E)) ∧
          (∏ s, (target s) ^ (multiplicity s)) ^ (r * E) ≤
            ∑ j, (((A j * B j * C j : ℕ) : ℝ) ^ tau) := by
  let localBase : Fin 15 → ℝ := fun s ↦
    (target s + componentBase tau s) / 2
  have hbase : ∀ s, 0 < localBase s := by
    intro s
    dsimp [localBase]
    have hcomponent := mme_dwz_square_componentBase_pos tau s
    have hs := htarget s
    linarith
  have htargetBase : ∀ s, target s < localBase s := by
    intro s
    dsimp [localBase]
    linarith [hstrict s]
  have hbaseComponent : ∀ s, localBase s < componentBase tau s := by
    intro s
    dsimp [localBase]
    linarith [hstrict s]
  apply mme_finite_HasTauValueAtLeast_common_power_multiplicity_product_below
    component multiplicity tau localBase target hbase htarget htargetBase
  intro s
  exact hlocal s (localBase s) (le_of_lt (hbase s)) (hbaseComponent s)

