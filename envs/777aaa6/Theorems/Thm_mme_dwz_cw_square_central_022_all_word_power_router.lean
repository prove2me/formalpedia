-- Prove2me | Theorems.Thm_mme_dwz_cw_square_central_022_all_word_power_router
-- name    : mme_dwz_cw_square_central_022_all_word_power_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T07:03:12.82663+00:00
-- url     : https://prove2.me/theorems/9bcfc6b7-9541-4ede-ab1e-5ab3df353a84
-- title:
--   All-word power router for the central 022 block
-- statement:
--   The source-faithful linear router from the central $022$ Coppersmith--Winograd block to $MM(1,1,q^2+2)$ extends functorially to every Kronecker power. For every word $w$ of length $n$ in the fine $022$ channel alphabet, the power map sends the corresponding source basis word to the matching matrix-multiplication basis word.
--
--   $$
--   F_n(T_{022}^{⊗ n}) = MM(1,1,q^2+2)^{⊗ n}; F_n(v_w)=e_w.
--   $$
--
--   The all-word clause, rather than only a prescribed-profile clause, permits a later coordinate projector to kill every forbidden component word.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, the central 022 restriction in Lemma 4.6; this theorem is its Kronecker-power lift.

import Definitions.Def_mme_dwz_cw_square_restricted_central_power_words
import Theorems.Thm_mme_dwz_cw_square_central_022_202_source_router

open PiTensorProduct TensorProduct
open MME MME.DWZFineChannel

universe u

set_option autoImplicit false

theorem mme_dwz_cw_square_central_022_all_word_power_router
    (K : Type u) [Field K] (q n : ℕ) :
    ∃ maps : ∀ s : Fin 3,
        ((Central022Block K q).kronPow n).V s →ₗ[K]
          ((MMObj K 1 1 (q ^ 2 + 2)).kronPow n).V s,
      PiTensorProduct.map maps ((Central022Block K q).kronPow n).t =
          ((MMObj K 1 1 (q ^ 2 + 2)).kronPow n).t ∧
      ∀ (w : Fin n → Fine022Channel q) (s : Fin 3),
        maps s (central022SourceWordVec K q n w s) =
          central022MMWordVec K q n w s := by
  sorry
