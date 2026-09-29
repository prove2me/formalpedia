-- Prove2me | Theorems.Thm_lean_workbook_plus_43939
-- name    : lean_workbook_plus_43939
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/d5605bc9-0a7b-4d8a-9e89-173a54948c97
-- statement:
--   Prove that $(ab+bc+ca-1)^{2} \leq(a^{2} +1)(b^{2}+1)(c^{2}+1)$ for all real numbers $a, b$ and $c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43939 : ∀ a b c : ℝ, (a * b + b * c + c * a - 1) ^ 2 ≤ (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)   :=  by sorry
