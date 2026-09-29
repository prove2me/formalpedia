-- Prove2me | Theorems.Thm_lean_workbook_plus_72028
-- name    : lean_workbook_plus_72028
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/ab52b730-c3a5-4277-8109-544998c53754
-- statement:
--   For $a\ge 1,b\ge 1,c\ge 1$ satisfied: $ab+bc+ca=4$ . Prove that $5a+4b+c\leq \frac{25}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72028 (a b c : ℝ) (hab : a ≥ 1 ∧ b ≥ 1 ∧ c ≥ 1) (h : a * b + b * c + c * a = 4) : 5 * a + 4 * b + c ≤ 25 / 2   :=  by sorry
