-- Prove2me | Theorems.Thm_mme_released_116_partition_parent_window
-- name    : mme_released_116_partition_parent_window
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:23:40.474506+00:00
-- url     : https://prove2.me/theorems/81515ae7-7500-4a03-83fa-07a0fa4cc1c5
-- title:
--   The released (1,1,6) regional windows imply its exact global histogram window
-- statement:
--   For the released owner-zero (1,1,6) component, there exists a partition of its d^4 parent positions into the six prescribed integer regions. In each of the three modes, regional parent typicality implies that every normalized full-word count differs by at most epsilon from the exact released joint-row marginal. Child words are obtained by the literal complete-word split. This proves window inclusion; it does not assert the full extraction or global numerical witness.
-- source:
--   Physical regional partitions and the released owner-zero (1,1,6) integer profiles.

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
set_option autoImplicit false


open MME.Released116 MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_116_partition_parent_window
    : ∃ positions : (Σ r : Fin 6, Fin (regionalSize r)) ≃ Fin (denominator ^ 4),
      ∀ (i : Fin 3) (f : Fin (denominator ^ 4) → CompleteWord 3) (eps : ℝ),
        parentTypical parent_total regionalSize splitCount (integerProfile i) eps
          (fun p =>
            let v := (completeWordSplitEquiv 2 (by decide)) (f (positions ⟨p.1,p.2.1⟩))
            ![v.1,v.2] p.2.2) →
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (denominator ^ 4) // f p = w} : ℝ) /
              (denominator : ℝ) ^ 4 -
            ((((ReleasedGlobal.jointRows 0 10).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by sorry
