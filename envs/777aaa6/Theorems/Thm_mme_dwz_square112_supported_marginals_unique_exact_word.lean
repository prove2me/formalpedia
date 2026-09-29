-- Prove2me | Theorems.Thm_mme_dwz_square112_supported_marginals_unique_exact_word
-- name    : mme_dwz_square112_supported_marginals_unique_exact_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T07:50:11.015497+00:00
-- url     : https://prove2.me/theorems/f006310c-3857-495c-8eea-c0049778cfe9
-- title:
--   Supported square112 marginal words uniquely reconstruct the exact four-row profile
-- statement:
--   Consider the four literal left fine-split rows of the canonical CW-square (1,1,2) constituent: (0,0,2), (0,1,1), (1,0,1), and (1,1,0). Fix any word length N and prescribed counts c₀,c₁,c₂,c₃. Suppose three mode words are coordinatewise supported on those four rows and have exactly the corresponding published marginal histograms. Then they are the mode words of a unique exact four-row word having precisely those prescribed counts. No extra count-sum or positivity hypothesis is necessary. The theorem includes zero length and zero row counts. This is a finite source reconstruction statement, not an assumed hashing closure or extraction condition.
-- source:
--   Duan–Wu–Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 (28 November 2023), https://arxiv.org/abs/2210.10173v5, Definition 3.7, the symmetric hashing discussion on printed pp.27–28, and the square112 restricted-splitting example in Section 6.3. The literal four-row data are public definition49aaeb9a-ebc2-471e-9310-97edb2a1c2b7; the exact all-mode histogram theorem is public Proved dd6159c3-48db-456b-9f6e-ebe7d462e681.

import Definitions.Def_mme_dwz_square112_exact_profile_data

open MME.DWZSquare112

set_option autoImplicit false

theorem mme_dwz_square112_supported_marginals_unique_exact_word
    (N : ℕ) (c : Fin 4 → ℕ) (x : Fin 3 → Fin N → Fin 3)
    (hsupport : ∀ j : Fin N, ∃ r : Fin 4, ∀ i : Fin 3, row r i = x i j)
    (hmarginal : ∀ i a : Fin 3,
      Fintype.card {j : Fin N // x i j = a} = marginal c i a) :
    ∃! w : ExactWord N c, modeWord w = x := by sorry
