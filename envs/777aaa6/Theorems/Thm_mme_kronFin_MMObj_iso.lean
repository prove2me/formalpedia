-- Prove2me | Theorems.Thm_mme_kronFin_MMObj_iso
-- name    : mme_kronFin_MMObj_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T03:23:20.058795+00:00
-- url     : https://prove2.me/theorems/fe30aace-f5bf-4e84-bb6f-7892fa471fa0
-- title:
--   A finite Kronecker product of matrix-multiplication tensors multiplies all dimensions
-- statement:
--   For a field $K$ and finite families of dimensions $(a_r),(b_r),(c_r)$, the ordered Kronecker product of the associated matrix-multiplication tensors is isomorphic to one matrix-multiplication tensor:
--
--   $$
--   \bigotimes_{r<R}\langle a_r,b_r,c_r\rangle
--   \cong
--   \left\langle\prod_{r<R}a_r,\prod_{r<R}b_r,\prod_{r<R}c_r\right\rangle.
--   $$
--
--   This is the finite-family form of multiplicativity of matrix multiplication. It turns a graded address block, assembled coordinate by coordinate, into the single matrix-multiplication summand used in laser-method extraction.
-- source:
--   Finite iteration of multiplicativity of matrix-multiplication tensors under Kronecker product.

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_tensor_bridge

open MME BigOperators

universe u

theorem mme_kronFin_MMObj_iso
    {K : Type u} [Field K] :
    ∀ (R : ℕ) (a b c : Fin R → ℕ),
      TensorObj.Isomorphic
        (TensorObj.kronFin R (fun r => MMObj K (a r) (b r) (c r)))
        (MMObj K (∏ r, a r) (∏ r, b r) (∏ r, c r)) := by
  sorry
