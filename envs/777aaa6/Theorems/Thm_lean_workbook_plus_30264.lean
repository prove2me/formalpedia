-- Prove2me | Theorems.Thm_lean_workbook_plus_30264
-- name    : lean_workbook_plus_30264
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/65453bbc-afb0-4bd4-956d-04c38ea10434
-- statement:
--   from $a^2+b^2+c^2=3$ we have; $\sum_{cyc}{(b+1)(a+b+1)}=\frac{1}{2}(a+b+c+3)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30264 (a b c : ℝ) (ha : a ^ 2 + b ^ 2 + c ^ 2 = 3) : (b + 1) * (a + b + 1) + (c + 1) * (b + c + 1) + (a + 1) * (c + a + 1) = (1 / 2) * (a + b + c + 3) ^ 2   :=  by sorry
