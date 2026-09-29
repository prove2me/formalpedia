-- Prove2me | Theorems.Thm_lean_workbook_plus_14003
-- name    : lean_workbook_plus_14003
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/270b3b5d-4560-4082-9d3f-7d13f7d3c385
-- statement:
--   Now $a>2$ . We can transform equation $x^2+axy+y^2 = 1$ into $(x+a\frac{y}{2})^2 - (a^2 - 4)(\frac{y}{2})^2 = 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14003 (a : ℝ) (ha : a > 2) (x y : ℝ) :  x^2 + a * x * y + y^2 = 1 ↔ (x + a * y / 2)^2 - (a^2 - 4) * (y / 2)^2 = 1   :=  by sorry
