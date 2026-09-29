-- Prove2me | Theorems.Thm_mme_released_116_scaled_parent_graded_fine_word_window
-- name    : mme_released_116_scaled_parent_graded_fine_word_window
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T00:33:50.045902+00:00
-- url     : https://prove2.me/theorems/a5e7b142-f07d-4880-9db6-6fcbe1c76ecc
-- title:
--   Parent grading and typicality imply the released 116 source window
-- statement:
--   The same child-position equivalence maps parent-graded typical words to the actual released source: exact parent grades and the prescribed global histogram window. No child split-address grading assumption is required.
-- source:
--   Released 116 recursive recipe interface: parent-grade source inclusion, concrete integer-step data, certified entropy budgets, and cofinal asymptotic growth.

import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_recursive_profiled_CW_data
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FinCases
import Theorems.Thm_mme_released_116_regional_total
import Theorems.Thm_mme_released_116_regional_split_mass
import Theorems.Thm_mme_released_116_weighted_parent_center
import Definitions.Def_mme_released_116_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Fin.Basic
open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
open MME.Released116 MME.MoreAsymmetryExactSeed MME.CompleteSplit
set_option autoImplicit false
universe u

theorem mme_released_116_scaled_parent_graded_fine_word_window (k : ℕ) (hk : 0 < k) :
    ∃ childPositions : Fin ((k * denominator ^ 4) * 2) ≃
        Position (fun r : Fin 6 => k * regionalSize r),
      ∀ (i : Fin 3)
        (x : ProfiledCW.FineWord ((k * denominator ^ 4) * 4)) (eps : ℝ),
        ParentGraded parent (fun r => k * regionalSize r) i (ProfiledCW.split childPositions
          (show ((k * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
            (k * denominator ^ 4) * 4 by omega) x) →
        parentTypical parent_total (fun r => k * regionalSize r)
          (fun r c => k * splitCount r c) (fun c w => k * integerProfile i c w) eps
          (ProfiledCW.split childPositions
            (show ((k * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
              (k * denominator ^ 4) * 4 by omega) x) →
        (∀ p : Fin (k * denominator ^ 4),
          (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl (Fin (k * denominator ^ 4))) rfl x p q).val)
            = parent 0 i) ∧
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * denominator ^ 4) //
              ProfiledCW.split (ell := 3) (Equiv.refl (Fin (k * denominator ^ 4))) rfl x p = w} : ℝ) /
              (k * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows 0 10).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by sorry
