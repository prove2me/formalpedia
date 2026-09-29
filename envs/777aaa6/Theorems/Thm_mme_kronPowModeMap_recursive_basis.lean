-- Prove2me | Theorems.Thm_mme_kronPowModeMap_recursive_basis
-- name    : mme_kronPowModeMap_recursive_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T14:37:38.502558+00:00
-- url     : https://prove2.me/theorems/858b2d80-0955-4179-be7f-693864994c6a
-- title:
--   A powered basis-labelled map acts letterwise on recursive words
-- statement:
--   Let a linear map send each vector of a chosen source basis to a vector of a chosen target basis according to a label map. Applying that same linear map independently in all factors of an arbitrary tensor power sends every recursive basis word to the recursive target word obtained by applying the label map at every position. This exact basis action is the bridge from a one-constituent router to word-level laser-method and hash-extraction arguments.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, tensor-power word restrictions in Sections 5–6; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_kron_pow_mode_word_basis
import Definitions.Def_mme_kron_pow_word_reindex

open MME MME.TensorObj MME.DWZComponentRestriction TensorProduct Module

universe u

set_option autoImplicit false

theorem mme_kronPowModeMap_recursive_basis
    {K : Type u} [Field K]
    {T S : TensorObj K 3} (i : Fin 3)
    {I J : Type u}
    (b : Basis I K (T.V i)) (c : Basis J K (S.V i))
    (f : T.V i →ₗ[K] S.V i) (label : I → J)
    (hf : ∀ a, f (b a) = c (label a)) :
    ∀ (n : ℕ) (w : PowIndex I n),
      kronPowModeMap i f n (kronPowModeBasis T i b n w) =
        kronPowModeBasis S i c n
          (PowIndex.ofFun n (fun r ↦ label (PowIndex.get n w r))) := by
  sorry
