-- Prove2me | Theorems.Thm_lean_workbook_plus_28570
-- name    : lean_workbook_plus_28570
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/c7dcf8bf-b283-4c80-b80d-90eec103302f
-- statement:
--   The probability that the second roll is different from the first one is $\frac 56$ , The probability that the third roll is different from the first two is $\frac46$ , and so on. The answer is $\frac56\cdot\frac46\cdot\frac36\cdot\frac26\cdot\frac16=\boxed{\frac5{324}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28570 :
  (5/6 * 4/6 * 3/6 * 2/6 * 1/6) = 5/324   :=  by sorry
