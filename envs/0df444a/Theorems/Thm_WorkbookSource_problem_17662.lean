-- Prove2me | Theorems.Thm_WorkbookSource_problem_17662
-- name    : WorkbookSource.problem_17662
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:04:40.27059+00:00
-- url     : https://prove2.me/theorems/ae03b16e-143b-4db9-8245-86d604dcfe55
-- title:
--   A quadratic-mean bound for four squared products
-- statement:
--   Using A.M.-G.M. inequality,
--    $$ \frac{\left((a^2+c^2)+(b^2+d^2)\right)^2}{4} \geq (a^2+c^2)(b^2+d^2) = a^2b^2+b^2c^2+c^2d^2+d^2a^2$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17662` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17662; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_17662 (a b c d : ℝ) : (a^2 + c^2 + b^2 + d^2)^2 / 4 ≥ a^2 * b^2 + b^2 * c^2 + c^2 * d^2 + d^2 * a^2  :=  by sorry
