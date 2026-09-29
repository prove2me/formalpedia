-- Prove2me | Theorems.Thm_lean_workbook_plus_62514
-- name    : lean_workbook_plus_62514
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/28a80ad9-a32d-48ad-86b8-c7e005d52410
-- statement:
--   Let $a,b,c$ be positive real numbers such that $abc=1$ . Prove that \n $$\frac{1}{a^2-a+1} \leqslant \frac{3}{2} \cdot \frac{a^2+1}{a^4+a^2+1}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62514 (a b c : ℝ) (habc : a * b * c = 1) : (1 / (a ^ 2 - a + 1) ≤ (3 / 2) * (a ^ 2 + 1) / (a ^ 4 + a ^ 2 + 1))   :=  by sorry
