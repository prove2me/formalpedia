-- Prove2me | Theorems.Thm_lean_workbook_plus_25262
-- name    : lean_workbook_plus_25262
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/9eb5fff4-70e7-4c49-b772-1a994d36e19a
-- statement:
--   Prove that $(2\sum ab - \sum {a^2})^2 \geq 3(2\sum{a^2b^2} - \sum {a^4})$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25262 (a b c: ℝ) : (2 * (a * b + b * c + c * a) - (a ^ 2 + b ^ 2 + c ^ 2)) ^ 2 ≥ 3 * (2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - (a ^ 4 + b ^ 4 + c ^ 4))   :=  by sorry
