-- Prove2me | Theorems.Thm_mme_kronFin_respects_iso
-- name    : mme_kronFin_respects_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T03:34:08.923384+00:00
-- url     : https://prove2.me/theorems/3994c8e7-1e9f-4296-b2bb-634be3294a68
-- title:
--   Finite ordered Kronecker products preserve pointwise tensor isomorphism
-- statement:
--   Let $(X_r)_{r<R}$ and $(Y_r)_{r<R}$ be two finite ordered families of tensors of the same order over a field. If $X_r$ is isomorphic to $Y_r$ for every coordinate $r$, then their ordered Kronecker products are isomorphic:
--
--   $$
--   \bigotimes_{r<R} X_r \cong \bigotimes_{r<R} Y_r.
--   $$
--
--   This is the finite functoriality principle used to assemble coordinatewise graded-block identifications into one address-block identification.
-- source:
--   Finite iteration of functoriality of the Kronecker product under tensor isomorphism.

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_tensor_quotient

open MME

universe u

theorem mme_kronFin_respects_iso
    {K : Type u} [Field K] {d : ℕ} :
    ∀ (R : ℕ) (X Y : Fin R → TensorObj K d),
      (∀ r, TensorObj.Isomorphic (X r) (Y r)) →
      TensorObj.Isomorphic
        (TensorObj.kronFin R X) (TensorObj.kronFin R Y) := by
  sorry
