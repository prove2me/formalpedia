-- Prove2me | Theorems.Thm_lean_workbook_plus_65043
-- name    : lean_workbook_plus_65043
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/0df981b8-eec2-4e94-b373-cbf46cfa7717
-- statement:
--   prove: $\frac{a+1}{b^2+1}+\frac{b+1}{c^2+1}+\frac{c+1}{a^2+1}\le a^2+b^2+c^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65043 : ∀ a b c : ℝ, (a + 1) / (b ^ 2 + 1) + (b + 1) / (c ^ 2 + 1) + (c + 1) / (a ^ 2 + 1) ≤ a ^ 2 + b ^ 2 + c ^ 2   :=  by sorry
