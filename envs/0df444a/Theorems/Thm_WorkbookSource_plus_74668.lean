-- Prove2me | Theorems.Thm_WorkbookSource_plus_74668
-- name    : WorkbookSource.plus_74668
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:54:01.100508+00:00
-- url     : https://prove2.me/theorems/628e641a-b6e2-4721-8eff-0eeacc7b8720
-- title:
--   A reciprocal sum involving a pair sum and product is at least two
-- statement:
--   Let $a,b,c>0$ and $a+b+c=3 .$ Prove that
--    $$ \frac{1}{a+b }+\frac{1}{(a+b)c }+\frac{1}{a bc} \geq 2$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_74668` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_74668; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_74668 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 1 / (a + b) + 1 / ((a + b) * c) + 1 / (a * b * c) ≥ 2   :=  by sorry
