-- Prove2me | Theorems.Thm_lean_workbook_plus_38958
-- name    : lean_workbook_plus_38958
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/a2999b24-2545-4931-b6c3-e686fff10840
-- statement:
--   Prove that $ab \leq \frac{1}{4}$ given $a + b = 1$ and $a, b \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38958 (a b : ℝ) (h1 : a + b = 1) (h2 : a >= 0 ∧ b >= 0) : a * b <= 1 / 4   :=  by sorry
