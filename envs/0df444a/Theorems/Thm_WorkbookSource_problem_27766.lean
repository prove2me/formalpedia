-- Prove2me | Theorems.Thm_WorkbookSource_problem_27766
-- name    : WorkbookSource.problem_27766
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:58.314895+00:00
-- url     : https://prove2.me/theorems/e5ded138-cc2f-404d-88d3-88482bb281a4
-- title:
--   A five-variable quadratic decomposition
-- statement:
--   Given the identity $(a+b+c+d+e)^2 - \frac{5}{2}(a(b+c)+b(c+d)+c(d+e)+d(e+a)+e(a+b)) = \frac{1}{16}(4e-d-c-b-a)^2 + \frac{15}{144}(3d-c-b-a)^2 + \frac{5}{24}(2c-b-a)^2 + \frac{5}{8}(b-a)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27766` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27766; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_27766 (a b c d e : ℝ) : (a + b + c + d + e) ^ 2 - (5 / 2) * (a * (b + c) + b * (c + d) + c * (d + e) + d * (e + a) + e * (a + b))  = (1 / 16) * (4 * e - d - c - b - a) ^ 2 + (15 / 144) * (3 * d - c - b - a) ^ 2 + (5 / 24) * (2 * c - b - a) ^ 2 + (5 / 8) * (b - a) ^ 2  :=  by sorry
