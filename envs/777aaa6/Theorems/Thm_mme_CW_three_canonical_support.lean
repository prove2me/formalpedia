-- Prove2me | Theorems.Thm_mme_CW_three_canonical_support
-- name    : mme_CW_three_canonical_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T05:26:37.700123+00:00
-- url     : https://prove2.me/theorems/af5087e0-64d7-4375-9091-9a23a4197be2
-- title:
--   The canonical three-grading of the Coppersmith--Winograd tensor has total grade two
-- statement:
--   Let $K$ be a field and let $CW_q$ carry its canonical three-grading, in which the distinguished $0$, middle, and terminal coordinates have grades $0$, $1$, and $2$. Every nonzero homogeneous block has total grade two. Equivalently, for every grade triple $\sigma : \{0,1,2\} \to \{0,1,2\}$,
--
--   $$
--   \sigma(0)+\sigma(1)+\sigma(2) \neq 2
--   \quad\Longrightarrow\quad
--   (CW_q)_\sigma = 0.
--   $$
--
--   This is the source-level support law used to control the two independent level-one halves of the squared Coppersmith--Winograd tensor before asymmetric hashing.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 6.1 and Claim 6.2; the underlying three-grading is the standard Coppersmith--Winograd decomposition. https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_cw_square_fine_split_grading

open MME
open MME.DWZStep1Support

universe u

set_option autoImplicit false

theorem mme_CW_three_canonical_support
    (K : Type u) [Field K] (q : ℕ) (sigma : Fin 3 → Fin 3)
    (hsum : (sigma 0).val + (sigma 1).val + (sigma 2).val ≠ 2) :
    (cwThreeCanonicalGrading K q).blockTensor sigma = 0 := by
  sorry
