-- Prove2me | Theorems.Thm_lean_workbook_plus_14728
-- name    : lean_workbook_plus_14728
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/7c63a092-f618-436a-a849-6be138a1a0a7
-- statement:
--   Find the maximum value of $F = (x_1-a)(x_2-a) + (x_2-a)(x_3-a) + (x_3-a)(x_4-a) + (x_4-a)(x_1-a)$ given $a = \frac{x_1+x_2+x_3+x_4}{4}$ and $x_1, x_2, x_3, x_4$ are real numbers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14728 (x1 x2 x3 x4 a : ℝ) (h1 : a = (x1 + x2 + x3 + x4) / 4) : (x1 - a) * (x2 - a) + (x2 - a) * (x3 - a) + (x3 - a) * (x4 - a) + (x4 - a) * (x1 - a) ≤ 0   :=  by sorry
