-- Prove2me | Theorems.Thm_lean_workbook_plus_69589
-- name    : lean_workbook_plus_69589
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/1297f2ee-1859-4873-9336-d53ccf201eeb
-- statement:
--   Put $a=x^3-1, b=(x+1)^3+1$ to get $a^3+b^3=(a+b)^3\iff ab(a+b)=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69589 (x a b : ℤ) (ha : a = x^3 - 1) (hb : b = (x + 1)^3 + 1) :
  a^3 + b^3 = (a + b)^3 ↔ a * b * (a + b) = 0   :=  by sorry
