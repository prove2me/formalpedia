-- Prove2me | Theorems.Thm_mme_stothers_phi233_square_support_pair_classification
-- name    : mme_stothers_phi233_square_support_pair_classification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:35:33.759384+00:00
-- url     : https://prove2.me/theorems/48f303ba-f5d0-4268-802b-aa8aeed62c2e
-- title:
--   Exact ten-pair square support of phi_233
-- statement:
--   If two supported canonical square-block grades add coordinatewise to $(2,3,3)$, then their ordered pair is exactly one of the ten displayed complementary pairs. These are the complete literal square-block support of $\varphi_{233}$; recording all ten is essential because this constituent has a nontrivial same-marginal family.
-- source:
--   Davie--Stothers (2013), Section 5 and Lemma 5.1(v), printed pp. 363-366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Data.Fin.Basic

set_option autoImplicit false

theorem mme_stothers_phi233_square_support_pair_classification
    (i₁ j₁ k₁ i₂ j₂ k₂ : Fin 5)
    (h₁ : i₁.val + j₁.val + k₁.val = 4)
    (h₂ : i₂.val + j₂.val + k₂.val = 4)
    (hi : i₁.val + i₂.val = 2)
    (hj : j₁.val + j₂.val = 3)
    (hk : k₁.val + k₂.val = 3) :
    (i₁ = 0 ∧ j₁ = 1 ∧ k₁ = 3 ∧ i₂ = 2 ∧ j₂ = 2 ∧ k₂ = 0) ∨
    (i₁ = 0 ∧ j₁ = 2 ∧ k₁ = 2 ∧ i₂ = 2 ∧ j₂ = 1 ∧ k₂ = 1) ∨
    (i₁ = 0 ∧ j₁ = 3 ∧ k₁ = 1 ∧ i₂ = 2 ∧ j₂ = 0 ∧ k₂ = 2) ∨
    (i₁ = 1 ∧ j₁ = 0 ∧ k₁ = 3 ∧ i₂ = 1 ∧ j₂ = 3 ∧ k₂ = 0) ∨
    (i₁ = 1 ∧ j₁ = 1 ∧ k₁ = 2 ∧ i₂ = 1 ∧ j₂ = 2 ∧ k₂ = 1) ∨
    (i₁ = 1 ∧ j₁ = 2 ∧ k₁ = 1 ∧ i₂ = 1 ∧ j₂ = 1 ∧ k₂ = 2) ∨
    (i₁ = 1 ∧ j₁ = 3 ∧ k₁ = 0 ∧ i₂ = 1 ∧ j₂ = 0 ∧ k₂ = 3) ∨
    (i₁ = 2 ∧ j₁ = 0 ∧ k₁ = 2 ∧ i₂ = 0 ∧ j₂ = 3 ∧ k₂ = 1) ∨
    (i₁ = 2 ∧ j₁ = 1 ∧ k₁ = 1 ∧ i₂ = 0 ∧ j₂ = 2 ∧ k₂ = 2) ∨
    (i₁ = 2 ∧ j₁ = 2 ∧ k₁ = 0 ∧ i₂ = 0 ∧ j₂ = 1 ∧ k₂ = 3) := by
  sorry
