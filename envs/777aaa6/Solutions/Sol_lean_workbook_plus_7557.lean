-- Prove2me | solution 1 for lean_workbook_plus_7557
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:58:55.922362+00:00
-- url     : https://prove2.me/submissions/95122cc5-9323-422a-a396-2cf9c21d473c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ : ℝ) : (a₁^2 + a₂^2 + a₃^2 + a₄^2 + a₅^2 + a₆^2 + a₇^2 + a₈^2) * (b₁^2 + b₂^2 + b₃^2 + b₄^2 + b₅^2 + b₆^2 + b₇^2 + b₈^2) = (a₁ * b₁ - a₂ * b₂ - a₃ * b₃ - a₄ * b₄ - a₅ * b₅ - a₆ * b₆ - a₇ * b₇ - a₈ * b₈)^2 + (a₁ * b₂ + a₂ * b₁ + a₃ * b₄ - a₄ * b₃ + a₅ * b₆ - a₆ * b₅ - a₇ * b₈ + a₈ * b₇)^2 + (a₁ * b₃ - a₂ * b₄ + a₃ * b₁ + a₄ * b₂ + a₅ * b₇ + a₆ * b₈ - a₇ * b₅ - a₈ * b₆)^2 + (a₁ * b₄ + a₂ * b₃ - a₃ * b₂ + a₄ * b₁ + a₅ * b₈ - a₆ * b₇ + a₇ * b₆ - a₈ * b₅)^2 + (a₁ * b₅ - a₂ * b₆ - a₃ * b₇ - a₄ * b₈ + a₅ * b₁ + a₆ * b₂ + a₇ * b₃ + a₈ * b₄)^2 + (a₁ * b₆ + a₂ * b₅ - a₃ * b₈ + a₄ * b₇ - a₅ * b₂ + a₆ * b₁ - a₇ * b₄ + a₈ * b₃)^2 + (a₁ * b₇ + a₂ * b₈ + a₃ * b₅ - a₄ * b₆ - a₅ * b₃ + a₆ * b₄ + a₇ * b₁ - a₈ * b₂)^2 + (a₁ * b₈ - a₂ * b₇ + a₃ * b₆ + a₄ * b₅ - a₅ * b₄ - a₆ * b₃ + a₇ * b₂ + a₈ * b₁)^2 := by
  (intros; linarith)
