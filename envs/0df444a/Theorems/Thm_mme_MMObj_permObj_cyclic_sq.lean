-- Prove2me | Theorems.Thm_mme_MMObj_permObj_cyclic_sq
-- name    : mme_MMObj_permObj_cyclic_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T03:36:27.22029+00:00
-- url     : https://prove2.me/theorems/f936e147-b49d-4c15-9e68-992e57457022
-- title:
--   Two cyclic mode permutations rotate matrix-multiplication dimensions twice
-- statement:
--   For a field $K$, applying the square of the cyclic mode permutation to the matrix-multiplication tensor with dimensions $(n,m,p)$ rotates its dimensions twice:
--
--   $$
--   \pi^2\langle n,m,p\rangle \cong \langle m,p,n\rangle.
--   $$
--
--   This gives the explicit dimension identification for the twice-permuted factor in cyclic symmetrization.
-- source:
--   Twice iterating the standard cyclic mode-permutation isomorphism for matrix-multiplication tensors.

import Definitions.Def_mme_permutation

open MME

universe u

theorem mme_MMObj_permObj_cyclic_sq
    {K : Type u} [Field K] (n m p : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K n m p))
      (MMObj K m p n) := by
  sorry
