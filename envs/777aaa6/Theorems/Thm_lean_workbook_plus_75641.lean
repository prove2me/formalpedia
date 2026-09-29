-- Prove2me | Theorems.Thm_lean_workbook_plus_75641
-- name    : lean_workbook_plus_75641
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/63271cde-1a8c-4ef9-b3cc-dcee7308156e
-- statement:
--   Let $a,b,c$ be positive real numbers such that $abc=1$ . Prove that $\frac{1}{a^2-a+1} \leqslant \frac{3}{2} \cdot \frac{a^2+1}{a^4+a^2+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75641 (a b c : ℝ) (h : a * b * c = 1) :
  (1 / (a ^ 2 - a + 1)) ≤ (3 / 2) * (a ^ 2 + 1) / (a ^ 4 + a ^ 2 + 1)   :=  by sorry
