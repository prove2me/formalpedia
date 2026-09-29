-- Prove2me | Theorems.Thm_mme_stothers_phi125_square_support_pair_classification
-- name    : mme_stothers_phi125_square_support_pair_classification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:35:22.419363+00:00
-- url     : https://prove2.me/theorems/8f8925b4-9da2-47d9-b663-f299ad3df096
-- title:
--   Exact six-pair square support of phi_125
-- statement:
--   If two supported canonical square-block grades, each of total degree four, add coordinatewise to $(1,2,5)$, then their ordered pair is exactly one of $(004,121)$, $(013,112)$, $(022,103)$ or the three reversed pairs. Thus the displayed six terms are the complete literal square-block support of $\varphi_{125}$.
-- source:
--   Davie--Stothers (2013), Section 5, displayed expansion of phi_125, printed p. 363, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Data.Fin.Basic

set_option autoImplicit false

theorem mme_stothers_phi125_square_support_pair_classification
    (i₁ j₁ k₁ i₂ j₂ k₂ : Fin 5)
    (h₁ : i₁.val + j₁.val + k₁.val = 4)
    (h₂ : i₂.val + j₂.val + k₂.val = 4)
    (hi : i₁.val + i₂.val = 1)
    (hj : j₁.val + j₂.val = 2)
    (hk : k₁.val + k₂.val = 5) :
    (i₁ = 0 ∧ j₁ = 0 ∧ k₁ = 4 ∧ i₂ = 1 ∧ j₂ = 2 ∧ k₂ = 1) ∨
    (i₁ = 0 ∧ j₁ = 1 ∧ k₁ = 3 ∧ i₂ = 1 ∧ j₂ = 1 ∧ k₂ = 2) ∨
    (i₁ = 0 ∧ j₁ = 2 ∧ k₁ = 2 ∧ i₂ = 1 ∧ j₂ = 0 ∧ k₂ = 3) ∨
    (i₁ = 1 ∧ j₁ = 0 ∧ k₁ = 3 ∧ i₂ = 0 ∧ j₂ = 2 ∧ k₂ = 2) ∨
    (i₁ = 1 ∧ j₁ = 1 ∧ k₁ = 2 ∧ i₂ = 0 ∧ j₂ = 1 ∧ k₂ = 3) ∨
    (i₁ = 1 ∧ j₁ = 2 ∧ k₁ = 1 ∧ i₂ = 0 ∧ j₂ = 0 ∧ k₂ = 4) := by
  sorry
