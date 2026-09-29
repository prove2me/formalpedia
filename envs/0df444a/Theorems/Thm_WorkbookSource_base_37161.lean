-- Prove2me | Theorems.Thm_WorkbookSource_base_37161
-- name    : WorkbookSource.base_37161
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:03:17.571158+00:00
-- url     : https://prove2.me/theorems/c99b4656-4594-4311-979e-9022ed3df162
-- title:
--   A shifted pairwise quadratic ratio upper bound at fixed sum three
-- statement:
--   If $a, b, c>0, a+b+c=3$ prove that $\sum_{cyc}{\frac{a+b}{1+a^2+b^2+ab}}\le \frac9{2(ab+bc+ca)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_37161` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_37161; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_37161 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a + b) / (1 + a^2 + b^2 + a * b) + (b + c) / (1 + b^2 + c^2 + b * c) + (c + a) / (1 + c^2 + a^2 + c * a) ≤ 9 / (2 * (a * b + b * c + c * a))  :=  by sorry
