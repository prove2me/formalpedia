-- Prove2me | Theorems.Thm_lean_workbook_plus_72066
-- name    : lean_workbook_plus_72066
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/be372116-edb4-4e30-9f8e-619df7de70d1
-- statement:
--   It is equivalent to $ \frac {1}{2}[(a - b)^6 + (b - c)^6 + (c - a)^6] + 2[ab(a - b)^4 + bc(b - c)^4 + ca(c - a)^4] + \frac {1}{2}(a^4(b-c)^2+b^4(c-a)^2+c^4(a-b)^2) \ge 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72066 {a b c : ℝ} : (1 / 2) * ((a - b) ^ 6 + (b - c) ^ 6 + (c - a) ^ 6) + 2 * (a * b * (a - b) ^ 4 + b * c * (b - c) ^ 4 + c * a * (c - a) ^ 4) + (1 / 2) * (a ^ 4 * (b - c) ^ 2 + b ^ 4 * (c - a) ^ 2 + c ^ 4 * (a - b) ^ 2) ≥ 0   :=  by sorry
