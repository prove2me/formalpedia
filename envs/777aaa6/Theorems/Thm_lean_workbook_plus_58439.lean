-- Prove2me | Theorems.Thm_lean_workbook_plus_58439
-- name    : lean_workbook_plus_58439
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/6243a460-0c53-41f2-aeda-c4d51b5a3ac9
-- statement:
--   prove that $\frac{1}{{{a^2} +{b^2}+3}} + \frac{1}{{{b^2} +{c^2}+3}} + \frac{1}{{{c^2} +{a^2}+3}} \le \frac{3}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58439 : ∀ a b c : ℝ, (1 / (a ^ 2 + b ^ 2 + 3) + 1 / (b ^ 2 + c ^ 2 + 3) + 1 / (c ^ 2 + a ^ 2 + 3)) ≤ 3 / 5   :=  by sorry
