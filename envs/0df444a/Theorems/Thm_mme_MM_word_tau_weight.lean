-- Prove2me | Theorems.Thm_mme_MM_word_tau_weight
-- name    : mme_MM_word_tau_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:43:30.83829+00:00
-- url     : https://prove2.me/theorems/ec100dc1-0b4e-474c-b944-1b6a25082e5e
-- title:
--   Exact tau-weight of the MM word expansion
-- statement:
--   For a finite family of matrix-multiplication shapes and any real `tau`, sum the tau-weighted volumes of all length-`r` words, where dimensions multiply along each word. The resulting total is exactly the `r`-th power of the original total tau-weight. The identity is valid without positivity assumptions on the natural-number dimensions.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.4 and the product-value bookkeeping in Section 6.3 and Equation (25), PDF pp. 13 and 59-60; https://arxiv.org/abs/2210.10173. Algebraically this is the finite word/multinomial expansion of the tau-weight sum.

import Mathlib.Tactic

open BigOperators

set_option autoImplicit false

theorem mme_MM_word_tau_weight
    {k r : ℕ} (a b c : Fin k → ℕ) (tau : ℝ) :
    (∑ p : Fin r → Fin k,
        ((((∏ t, a (p t)) * (∏ t, b (p t)) * (∏ t, c (p t)) : ℕ) : ℝ) ^ tau)) =
      (∑ i : Fin k, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) ^ r := by sorry
