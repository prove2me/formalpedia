-- Prove2me | Theorems.Thm_lean_workbook_plus_70105
-- name    : lean_workbook_plus_70105
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/9d241a1a-6aa0-4cdd-aa34-010b237ee087
-- statement:
--   Prove that $abc(a^3+b^3+c^3-3abc) \geqslant (a^2-bc)(b^2-ca)(c^2-ab)$ for all $a,\,b,\,c$ are real numbers such that $ab+bc+ca \geqslant 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70105 : ∀ a b c : ℝ, (ab + bc + ca ≥ 0 → a * b * c * (a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c) ≥ (a ^ 2 - b * c) * (b ^ 2 - c * a) * (c ^ 2 - a * b))   :=  by sorry
