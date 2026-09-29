-- Prove2me | Theorems.Thm_mme_kron_power_position_permutation_basis_transport
-- name    : mme_kron_power_position_permutation_basis_transport
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:34:08.955245+00:00
-- url     : https://prove2.me/theorems/c6465b54-d031-4b69-a0cc-2e428d7a7ed1
-- title:
--   Permuting tensor-power positions preserves the tensor and word coordinates
-- statement:
--   For a three-mode tensor $T$ over any field, choose a basis in each mode. For every $n\ge 0$ and permutation $e$ of the $n$ positions, there are modewise linear automorphisms preserving $T^{\otimes n}$. Each automorphism permutes the corresponding word basis, and the resulting word at position $r$ has the original word's coordinate at $e^{-1}(r)$. The same position permutation is used in every mode. This supplies both tensor invariance and the coordinate identities needed to transport word filters.
-- source:
--   Tensor-power position permutation and the accepted common-halving joined filtered source restriction.

import Definitions.Def_mme_kron_pow_mode_word_basis
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_kron_power_position_permutation_basis_transport
    {K : Type u} [Field K] (T : TensorObj K 3)
    {α : Fin 3 → Type u} (b : ∀ i, Basis (α i) K (T.V i))
    (n : ℕ) (e : Equiv.Perm (Fin n)) :
    ∃ F : ∀ i, (T.kronPow n).V i ≃ₗ[K] (T.kronPow n).V i,
      PiTensorProduct.map (fun i => (F i).toLinearMap) (T.kronPow n).t =
        (T.kronPow n).t ∧
      ∀ i, ∃ perm : Equiv.Perm (PowIndex (α i) n),
        (∀ w, F i (kronPowModeBasis T i (b i) n w) =
          kronPowModeBasis T i (b i) n (perm w)) ∧
        (∀ w r, PowIndex.get n (perm w) r = PowIndex.get n w (e.symm r)) := by sorry
