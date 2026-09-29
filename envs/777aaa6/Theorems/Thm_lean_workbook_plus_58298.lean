-- Prove2me | Theorems.Thm_lean_workbook_plus_58298
-- name    : lean_workbook_plus_58298
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/26461030-880a-4336-93e6-83f8412945e1
-- statement:
--   Prove that $(ab+bc+ca)(a+b+c) \leq \frac{9}{8}(a+b)(b+c)(c+a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58298 : ∀ a b c : ℝ, (a * b + b * c + c * a) * (a + b + c) ≤ (9 / 8) * (a + b) * (b + c) * (c + a)   :=  by sorry
