-- Prove2me | Theorems.Thm_lean_workbook_plus_55988
-- name    : lean_workbook_plus_55988
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/f80af158-35aa-4a0c-80cf-fd374569a769
-- statement:
--   Let $a, b, c, d$ be non-negative numbers such that $a+b+c+d \ge 4$ and $abcd \ge 1$. Prove that $(a+b+c+d)^2 + 48abcd \ge 64$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55988 (a b c d : ℝ) (h1 : a + b + c + d >= 4) (h2 : a * b * c * d >= 1) : (a + b + c + d) ^ 2 + 48 * a * b * c * d >= 64   :=  by sorry
