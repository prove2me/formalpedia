-- Prove2me | Theorems.Thm_mme_stothers_phi134_square_support_pair_classification
-- name    : mme_stothers_phi134_square_support_pair_classification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:35:24.016434+00:00
-- url     : https://prove2.me/theorems/0e58de7e-9297-4695-90e8-352da3260c1c
-- title:
--   Exact eight-pair square support of phi_134
-- statement:
--   If two supported canonical square-block grades add coordinatewise to $(1,3,4)$, their ordered pair is exactly one of $(004,130)$, $(013,121)$, $(022,112)$, $(031,103)$ or the four reversed pairs. These eight pairs are therefore the complete literal square-block support of $\varphi_{134}$.
-- source:
--   Davie--Stothers (2013), Section 5 and Lemma 5.1(iii), printed pp. 363-365, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Data.Fin.Basic

set_option autoImplicit false

theorem mme_stothers_phi134_square_support_pair_classification
    (i₁ j₁ k₁ i₂ j₂ k₂ : Fin 5)
    (h₁ : i₁.val + j₁.val + k₁.val = 4)
    (h₂ : i₂.val + j₂.val + k₂.val = 4)
    (hi : i₁.val + i₂.val = 1)
    (hj : j₁.val + j₂.val = 3)
    (hk : k₁.val + k₂.val = 4) :
    (i₁ = 0 ∧ j₁ = 0 ∧ k₁ = 4 ∧ i₂ = 1 ∧ j₂ = 3 ∧ k₂ = 0) ∨
    (i₁ = 0 ∧ j₁ = 1 ∧ k₁ = 3 ∧ i₂ = 1 ∧ j₂ = 2 ∧ k₂ = 1) ∨
    (i₁ = 0 ∧ j₁ = 2 ∧ k₁ = 2 ∧ i₂ = 1 ∧ j₂ = 1 ∧ k₂ = 2) ∨
    (i₁ = 0 ∧ j₁ = 3 ∧ k₁ = 1 ∧ i₂ = 1 ∧ j₂ = 0 ∧ k₂ = 3) ∨
    (i₁ = 1 ∧ j₁ = 0 ∧ k₁ = 3 ∧ i₂ = 0 ∧ j₂ = 3 ∧ k₂ = 1) ∨
    (i₁ = 1 ∧ j₁ = 1 ∧ k₁ = 2 ∧ i₂ = 0 ∧ j₂ = 2 ∧ k₂ = 2) ∨
    (i₁ = 1 ∧ j₁ = 2 ∧ k₁ = 1 ∧ i₂ = 0 ∧ j₂ = 1 ∧ k₂ = 3) ∨
    (i₁ = 1 ∧ j₁ = 3 ∧ k₁ = 0 ∧ i₂ = 0 ∧ j₂ = 0 ∧ k₂ = 4) := by
  sorry
