-- Prove2me | Definitions.Def_mme_basis_index_permutation
-- name    : mme_basis_index_permutation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T08:20:05.142623+00:00
-- url     : https://prove2.me/theorems/f5968cd2-8aa4-4313-bcb0-590ac488ae96
-- title:
--   Linear equivalence induced by a basis-index permutation
-- statement:
--   Let a vector space have a basis indexed by a type $I$. Every permutation $e:I\simeq I$ induces a linear automorphism sending the basis vector $b_i$ to $b_{e(i)}$. The same definition specializes to recursive tensor-power word bases, where a permutation of positions gives an equivalence of word indices whose inverse is induced by the inverse position permutation.
--
--   This is the variable-level linear map required to lift the DWZ standard-form block shuffle from word indices to mode spaces.
--
--   **Formalization Note** The automorphism is defined through finitely supported basis coordinates, so it is valid without selecting an ordering of the basis indices.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claim 5.9, PDF pp. 49--50 / printed pp. 48--49; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kron_pow_word_reindex
import Mathlib.LinearAlgebra.Basis.Submodule

open Module

universe u

namespace MME.DWZComponentRestriction

set_option autoImplicit false
set_option warningAsError true

variable {K : Type u} [Field K]

/-- Reindexing recursive words is an equivalence, with inverse induced by the
inverse position permutation. -/
def PowIndex.reindexEquiv {ι : Type u} {n : ℕ}
    (e : Equiv.Perm (Fin n)) : PowIndex ι n ≃ PowIndex ι n where
  toFun := PowIndex.reindex e
  invFun := PowIndex.reindex e.symm
  left_inv := PowIndex.reindex_symm_reindex e
  right_inv := by
    intro w
    simpa using PowIndex.reindex_symm_reindex e.symm w

/-- The linear equivalence which sends each member of a basis to the member
whose index is its image under `e`. -/
noncomputable def basisIndexPermEquiv
    {V : Type u} [AddCommGroup V] [Module K V]
    {ι : Type u} (b : Basis ι K V) (e : ι ≃ ι) : V ≃ₗ[K] V :=
  b.repr.trans ((Finsupp.domLCongr e).trans b.repr.symm)

@[simp] theorem basisIndexPermEquiv_apply_basis
    {V : Type u} [AddCommGroup V] [Module K V]
    {ι : Type u} (b : Basis ι K V) (e : ι ≃ ι) (j : ι) :
    basisIndexPermEquiv b e (b j) = b (e j) := by
  simp [basisIndexPermEquiv, LinearEquiv.trans_apply]

end MME.DWZComponentRestriction


