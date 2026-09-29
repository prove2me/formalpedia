-- Prove2me | Theorems.Thm_mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
-- name    : mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:49:25.313719+00:00
-- url     : https://prove2.me/theorems/7c76a30a-da26-41d3-bea4-2389030922df
-- title:
--   A mismatched grade kills a tensor-power basis word under address projection
-- statement:
--   Let a basis of one tensor mode be labelled by grading classes, and suppose every one-letter block projection kills basis vectors carrying a different class. In any tensor power, the projector attached to an address kills every canonical basis word that disagrees with that address at even one position. This is the exact basis-level zeroing law used to show that a hash extraction factors through an allowed-word subspace.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, the word zeroing and primary-hash extraction in Sections 5–6; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_kron_pow_mode_word_basis
import Mathlib.LinearAlgebra.TensorProduct.Basis

open MME Module TensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t : ℕ} {ι : Type u}
    (G : T.TypeGrading t) (i : Fin 3)
    (b : Basis ι K (T.V i)) (grade : ι → Fin t)
    (hzero : ∀ (a : Fin t) (j : ι), grade j ≠ a →
      G.blockProj i a (b j) = 0) :
    ∀ (n : ℕ) (address : Fin 3 → Fin n → Fin t)
      (w : PowIndex ι n),
      (∃ r : Fin n, grade (PowIndex.get n w r) ≠ address i r) →
      gradedAddressProj G n address i
          (kronPowModeBasis T i b n w) = 0 := by
  sorry
