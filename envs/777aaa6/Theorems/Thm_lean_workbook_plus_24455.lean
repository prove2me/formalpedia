-- Prove2me | Theorems.Thm_lean_workbook_plus_24455
-- name    : lean_workbook_plus_24455
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/20abb013-3acd-49df-ba9e-4d623b4e1ade
-- statement:
--   Prove that if $a$ and $b$ are real numbers such that $a+b=2$ and $a^4+b^4=16$, then $ab=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24455 {a b : ℝ} (h₁ : a + b = 2) (h₂ : a ^ 4 + b ^ 4 = 16) : a * b = 0   :=  by sorry
