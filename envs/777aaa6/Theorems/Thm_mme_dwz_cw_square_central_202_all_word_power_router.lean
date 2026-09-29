-- Prove2me | Theorems.Thm_mme_dwz_cw_square_central_202_all_word_power_router
-- name    : mme_dwz_cw_square_central_202_all_word_power_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T07:03:15.113549+00:00
-- url     : https://prove2.me/theorems/fcfc36ba-3da3-4cf4-816b-4888877acbb6
-- title:
--   All-word power router for the central 202 block
-- statement:
--   The cyclically rotated source-faithful router from the central $202$ block to $MM(q^2+2,1,1)$ extends to every Kronecker power and preserves the exact label of every fine-channel basis word.
--
--   $$
--   G_n(T_{202}^{⊗ n}) = MM(q^2+2,1,1)^{⊗ n}; G_n(v_w)=e_w.
--   $$
--
--   This is the rotated all-word interface needed to project the row-$10$ component onto its allowed restricted-word family.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, the central 202 restriction in Lemma 4.6; this theorem is its Kronecker-power lift.

import Definitions.Def_mme_dwz_cw_square_restricted_central_power_words
import Theorems.Thm_mme_dwz_cw_square_central_022_202_source_router

open PiTensorProduct TensorProduct
open MME MME.DWZFineChannel

universe u

set_option autoImplicit false

theorem mme_dwz_cw_square_central_202_all_word_power_router
    (K : Type u) [Field K] (q n : ℕ) :
    ∃ maps : ∀ s : Fin 3,
        ((Central202Block K q).kronPow n).V s →ₗ[K]
          ((MMObj K (q ^ 2 + 2) 1 1).kronPow n).V s,
      PiTensorProduct.map maps ((Central202Block K q).kronPow n).t =
          ((MMObj K (q ^ 2 + 2) 1 1).kronPow n).t ∧
      ∀ (w : Fin n → Fine202Channel q) (s : Fin 3),
        maps s (central202SourceWordVec K q n w s) =
          central202MMWordVec K q n w s := by
  sorry
