-- Prove2me | Theorems.Thm_mme_perm_kronPow_mode_equiv_preserves_tensor
-- name    : mme_perm_kronPow_mode_equiv_preserves_tensor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:43:59.164435+00:00
-- url     : https://prove2.me/theorems/78840018-6aa1-4729-9d11-af4bc22a9493
-- title:
--   The canonical mode equivalence preserves permuted tensor powers
-- statement:
--   Let $T$ be an order-three tensor, let $e$ permute its modes, and let $n$ be a nonnegative integer. Apply the canonical recursive mode equivalences from $(eT)^{\otimes n}$ to the $e^{-1}$-indexed modes of $T^{\otimes n}$. Their tensor product sends the tensor of $(eT)^{\otimes n}$ exactly to the mode-reindexing of the tensor of $T^{\otimes n}$:
--
--   $$
--   \bigotimes_i E_{e,T,n,i}igl((eT)^{\otimes n}igr)=e\bigl(T^{\otimes n}\bigr).
--   $$
--
--   This naturality theorem permits exact restriction maps and basis formulas to pass through cyclic mode permutations at arbitrary power, rather than retaining only an abstract isomorphism class.
-- source:
--   Standard naturality of tensor powers under mode reindexing; formalization infrastructure for the q=6 Coppersmith-Winograd 121/211 rows.

import Definitions.Def_mme_perm_kronPow_mode_equiv

open MME PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_perm_kronPow_mode_equiv_preserves_tensor
    {K : Type u} [Field K] (e : Equiv.Perm (Fin 3))
    (T : TensorObj K 3) (n : ℕ) :
    PiTensorProduct.map
        (fun i ↦ (MME.TensorObj.permKronPowModeEquiv e T i n).toLinearMap)
        ((TensorObj.permObj e T).kronPow n).t =
      (TensorObj.permObj e (T.kronPow n)).t := by
  sorry
