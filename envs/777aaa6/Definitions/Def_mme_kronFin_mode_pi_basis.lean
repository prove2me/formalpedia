-- Prove2me | Definitions.Def_mme_kronFin_mode_pi_basis
-- name    : mme_kronFin_mode_pi_basis
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T09:02:12.547032+00:00
-- url     : https://prove2.me/theorems/d1d58045-44bf-4051-88da-87f8249936bd
-- title:
--   Function-indexed mode basis of a heterogeneous finite Kronecker product
-- statement:
--   Let $K$ be a field and let $X_0,\ldots,X_{n-1}$ be tensor objects with the same number of modes. Fix one mode $i$. If the $i$th mode of each factor $X_j$ has a basis indexed by a type $I_j$, then the corresponding mode of the ordered finite Kronecker product has a canonical tensor-product basis indexed by the dependent product
--
--   $$
--   \prod_{j=0}^{n-1} I_j.
--   $$
--
--   The construction follows the recursive parenthesization of the ordered Kronecker product and reindexes its nested product basis as an ordinary dependent function. For $n=0$, it is the singleton basis of the scalar mode of the tensor unit. This generic linear-algebra interface does not form a tensor direct sum.
-- source:
--   Standard tensor-product basis construction; applied here to the ordered Kronecker products in Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2--5.4; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_CW_2376_address_block
import Mathlib.LinearAlgebra.TensorProduct.Basis

open MME Module TensorProduct

universe u

namespace MME.TensorObj

set_option autoImplicit false
set_option warningAsError true

/-- A heterogeneous family of chosen mode bases induces a function-indexed
basis of the corresponding ordered finite Kronecker product. -/
noncomputable def kronFinModePiBasis
    {K : Type u} [Field K] {d : ℕ} :
    (n : ℕ) →
    (X : Fin n → TensorObj K d) →
    (i : Fin d) →
    {index : Fin n → Type u} →
    (∀ j, Basis (index j) K ((X j).V i)) →
    Basis (∀ j, index j) K ((TensorObj.kronFin n X).V i)
  | 0, _, _, index, _ => by
      change Basis (∀ j : Fin 0, index j) K K
      exact Basis.singleton (∀ j : Fin 0, index j) K
  | n + 1, X, i, index, b => by
      letI : IsScalarTower K K ((X 0).V i) :=
        IsScalarTower.of_algebraMap_smul (by simp)
      exact (Module.Basis.tensorProduct (b 0)
        (kronFinModePiBasis n (fun j ↦ X j.succ) i
          (fun j ↦ b j.succ))).reindex (Fin.consEquiv index)

end MME.TensorObj


