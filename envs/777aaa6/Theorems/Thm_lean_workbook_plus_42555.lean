-- Prove2me | Theorems.Thm_lean_workbook_plus_42555
-- name    : lean_workbook_plus_42555
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/eb7aff51-bcf8-4c21-a1d7-3a3b7b52a750
-- statement:
--   Prove that if $a, b, c \in \mathbb{R}$ with $b < c$, $b + c < a + 1$, and $a > 1$, then $b < a$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42555 (a b c : ℝ) (h₁ : b < c) (h₂ : b + c < a + 1) (h₃ : a > 1) : b < a   :=  by sorry
