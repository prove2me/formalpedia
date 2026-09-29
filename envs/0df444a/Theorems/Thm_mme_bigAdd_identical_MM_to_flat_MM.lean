-- Prove2me | Theorems.Thm_mme_bigAdd_identical_MM_to_flat_MM
-- name    : mme_bigAdd_identical_MM_to_flat_MM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-06-05T01:34:30.761671+00:00
-- url     : https://prove2.me/theorems/7681a776-11a1-4d98-8553-b1fbf990e8d7
-- statement:
--   The matrix-multiplication tensor MMObj(k·a, b, c) is a restriction (degeneration) of the direct sum of k identical copies of MMObj(a, b, c). A paper-agnostic building block: folds k parallel identical MM blocks into a single MM of k-times-larger first dimension.

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_mme_tensor
import Definitions.Def_mme_tensor_rank
open MME BigOperators
universe u

theorem mme_bigAdd_identical_MM_to_flat_MM
    {K : Type u} [Field K] (k a b c : ℕ) :
    TensorObj.Restrict
      (MMObj K (k * a) b c)
      (TensorObj.bigAdd (fun _ : Fin k => MMObj K a b c)) := by sorry
