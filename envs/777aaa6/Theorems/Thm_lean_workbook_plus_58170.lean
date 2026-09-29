-- Prove2me | Theorems.Thm_lean_workbook_plus_58170
-- name    : lean_workbook_plus_58170
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/52fa3ef2-22ec-4f45-9de9-cfa7cb965359
-- statement:
--   $(ab + bc + ca) \left(\frac {1}{(a + b)^2} + \frac {1}{(b + c)^2} + \frac {1}{(c + a)^2}\right) \ge \frac {9}{4} \Leftrightarrow \sum_{sym}(4a^5b - a^4b^2 - 3a^3b^3 + a^4bc - 2a^3b^2c + a^2b^2c^2) \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58170 :  ∀ a b c : ℝ, (a * b + b * c + c * a) * (1 / (a + b) ^ 2 + 1 / (b + c) ^ 2 + 1 / (c + a) ^ 2) ≥ 9 / 4 ↔   ∑ x in {a, b, c}, ∑ y in {a, b, c}, ∑ z in {a, b, c}, (4 * x ^ 5 * y - x ^ 4 * y ^ 2 - 3 * x ^ 3 * y ^ 3 + x ^ 4 * y * z - 2 * x ^ 3 * y ^ 2 * z + x ^ 2 * y ^ 2 * z ^ 2) ≥ 0   :=  by sorry
