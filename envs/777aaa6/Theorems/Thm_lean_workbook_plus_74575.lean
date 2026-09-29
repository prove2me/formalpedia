-- Prove2me | Theorems.Thm_lean_workbook_plus_74575
-- name    : lean_workbook_plus_74575
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/c3e2096a-90a5-4618-907f-c0ca0b9d0c16
-- statement:
--   Given $a, b, c \geq 0$, prove the following identity for degree 3:\n$(a + \frac{b + c}{4}) \sum a(a - b)(a - c) = bc(b - c)^2 + \frac{ca(c - a)^2 + ab(a - b)^2}{4} + \frac{(2a^2 - b^2 - c^2 - ab + 2bc - ca)^2}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74575 (a b c : ℝ) : (a + (b + c) / 4) * (a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b)) = b * c * (b - c) ^ 2 + (c * a * (c - a) ^ 2 + a * b * (a - b) ^ 2) / 4 + (2 * a ^ 2 - b ^ 2 - c ^ 2 - a * b + 2 * b * c - c * a) ^ 2 / 4   :=  by sorry
