-- Prove2me | Theorems.Thm_mme_released_interior_scaled_graded_fine_word_window
-- name    : mme_released_interior_scaled_graded_fine_word_window
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T05:12:38.724162+00:00
-- url     : https://prove2.me/theorems/47e4a0f7-cf71-400b-8090-52f1cb4ce238
-- title:
--   Child grading and regional windows imply the graded global fine-word window
-- statement:
--   A single child-position order identifies regional child words with literal halves of the same fine word. Child grading and regional typicality imply exact parent grades and the released global histogram window. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_released_interior_scaled_partition_parent_window
import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_complete_split_concatenation
import Definitions.Def_mme_released_interior_integer_profiles
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization
open scoped Classical

theorem mme_released_interior_scaled_graded_fine_word_window
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (k : ℕ) (hk : 0 < k) :
    ∃ childPositions : Fin ((k * denominator ^ 4) * 2) ≃
        Position (fun r : Fin 6 => k * (regionalSize owner s) r),
      ∀ (i : Fin 3) (a : Address 4 6 (parent s) (fun r => k * (regionalSize owner s) r))
        (x : ProfiledCW.FineWord ((k * denominator ^ 4) * 4)) (eps : ℝ),
        Graded (parent_total s) i a (ProfiledCW.split childPositions
          (show ((k * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
            (k * denominator ^ 4) * 4 by omega) x) →
        parentTypical (parent_total s) (fun r => k * (regionalSize owner s) r)
          (fun r c => k * (splitCount owner s) r c) (fun c w => k * (integerProfile owner s) i c w) eps
          (ProfiledCW.split childPositions
            (show ((k * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
              (k * denominator ^ 4) * 4 by omega) x) →
        (∀ p : Fin (k * denominator ^ 4),
          (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl (Fin (k * denominator ^ 4))) rfl x p q).val)
            = (parent s) 0 i) ∧
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * denominator ^ 4) //
              ProfiledCW.split (ell := 3) (Equiv.refl (Fin (k * denominator ^ 4))) rfl x p = w} : ℝ) /
              (k * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows owner s).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by sorry
