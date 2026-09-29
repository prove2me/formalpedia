-- Prove2me | Theorems.Thm_mme_dwz_table2_fifteen_multiplicity_common_power_product_of_local_strict_values
-- name    : mme_dwz_table2_fifteen_multiplicity_common_power_product_of_local_strict_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T07:13:40.908485+00:00
-- url     : https://prove2.me/theorems/7c95295e-07e7-4805-9fac-8d128ffbc50d
-- title:
--   Fifteen-slot Table-2 common-power product interface
-- statement:
--   Let fifteen literal tensor objects represent the fifteen Table-2 component slots, with prescribed integral occurrence multiplicities. Suppose every nonnegative value strictly below the printed base of a slot is witnessed as a tau-value lower bound on that actual component object. Then any chosen nonnegative strict local targets synchronize on one positive integral exponent lattice, and the powered multiplicity-weighted component product genuinely restricts to a finite MM direct sum with total tau-weight at least the corresponding weighted target product. The component objects remain explicit inputs, so the theorem is an interface for—not an assumption of—the Z-restricted source construction.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6.3, Table 2, and Equation (25), PDF pp. 59-60; https://arxiv.org/abs/2210.10173. The statement isolates the exact value-side premise expected from the literal Z-restricted component projection branch.

import Mathlib.Tactic
import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_dwz_square_componentBase_pos
import Theorems.Thm_mme_finite_HasTauValueAtLeast_common_power_multiplicity_product_below

open MME BigOperators MME.DWZSquare

set_option autoImplicit false

universe u

theorem mme_dwz_table2_fifteen_multiplicity_common_power_product_of_local_strict_values
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
            ∑ j, (((A j * B j * C j : ℕ) : ℝ) ^ tau) := by sorry
