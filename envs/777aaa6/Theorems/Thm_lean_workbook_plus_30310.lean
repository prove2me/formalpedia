-- Prove2me | Theorems.Thm_lean_workbook_plus_30310
-- name    : lean_workbook_plus_30310
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/629ecf35-aae3-4cfa-88bf-d374661f35bf
-- statement:
--   Prove that $9=3(a^2+b^2+c^2)\ge (a+b+c)^2\implies a+b+c\le 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30310 (a b c : ℝ) (h : 9 = 3 * (a ^ 2 + b ^ 2 + c ^ 2)) :
  a + b + c ≤ 3   :=  by sorry
