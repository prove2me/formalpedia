-- Prove2me | Theorems.Thm_mme_MMObj_restrict_oneObj_iff
-- name    : mme_MMObj_restrict_oneObj_iff
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T07:01:40.13064+00:00
-- url     : https://prove2.me/theorems/8941d7c4-7901-48ab-b104-4a5810183529
-- title:
--   Matrix multiplication tensors obtainable from a scalar unit
-- statement:
--   Over any field, the matrix multiplication tensor of dimensions a, b, c is a restriction of the scalar unit tensor if and only if a*b*c is at most one. This includes zero dimensions. For positive dimensions, only a=b=c=1 is possible.
-- source:
--   Direct construction for volumes zero and one, and flattening-rank monotonicity for necessity.

import Definitions.Def_mme_tensor_rank
open MME
universe u
set_option autoImplicit false

theorem mme_MMObj_restrict_oneObj_iff {K : Type u} [Field K] (a b c : ℕ) :
    TensorObj.Restrict (MMObj K a b c) (TensorObj.oneObj : TensorObj K 3) ↔
      a * b * c ≤ 1 := by sorry
