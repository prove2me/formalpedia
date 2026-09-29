-- Prove2me | Theorems.Thm_mme_permuted_power_word_basis_transport
-- name    : mme_permuted_power_word_basis_transport
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:00:58.418748+00:00
-- url     : https://prove2.me/theorems/6d086421-97b5-4417-8bae-d4cfd5412eb3
-- title:
--   Basis-preserving tensor maps lift through permuted powers
-- statement:
--   Let X and Y be order-three tensors over a field and let e permute the modes. Suppose modewise linear maps f take e(X) to Y and send a chosen basis of each reindexed mode of X to an equally indexed basis of Y. For every nonnegative n, there are modewise linear maps taking e(X to the n-th Kronecker power) to the n-th Kronecker power of Y. These maps send every recursive tensor-product basis word to the word with the same indices in the target basis. This retains the word coordinates needed when transporting basis projections.
-- source:
--   Naturality of tensor mode reindexing under Kronecker products and modewise linear maps.

import Definitions.Def_mme_permutation
import Definitions.Def_mme_kron_pow_mode_word_basis
import Definitions.Def_mme_TypeGrading_kron

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_permuted_power_word_basis_transport
    {K : Type u} [Field K] {X Y : TensorObj K 3}
    (e : Equiv.Perm (Fin 3))
    (f : ∀ i, (TensorObj.permObj e X).V i →ₗ[K] Y.V i)
    (hf : PiTensorProduct.map f (TensorObj.permObj e X).t = Y.t)
    {ι : Fin 3 → Type u}
    (b : ∀ i, Basis (ι i) K (X.V (e.symm i)))
    (c : ∀ i, Basis (ι i) K (Y.V i))
    (hb : ∀ i a, f i (b i a) = c i a) (n : ℕ) :
    ∃ F : ∀ i, (TensorObj.permObj e (X.kronPow n)).V i →ₗ[K] (Y.kronPow n).V i,
      PiTensorProduct.map F (TensorObj.permObj e (X.kronPow n)).t =
        (Y.kronPow n).t ∧
      ∀ i (w : PowIndex (ι i) n),
        F i (kronPowModeBasis X (e.symm i) (b i) n w) =
          kronPowModeBasis Y i (c i) n w := by sorry
