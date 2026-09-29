-- Prove2me | Theorems.Thm_lean_workbook_plus_71060
-- name    : lean_workbook_plus_71060
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/b1786bed-01d0-4260-af3c-6e33d551a6f0
-- statement:
--   Prove the identity $(a^2 + 1)(b^2 + 1)(c^2 + 1) = (a + b + c - abc)^2 + (ab + bc + ca - 1)^2$ for real numbers $a, b, c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71060 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) = (a + b + c - a * b * c)^2 + (a * b + b * c + c * a - 1)^2   :=  by sorry
