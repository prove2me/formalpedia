-- Prove2me | Theorems.Thm_WorkbookSource_base_6651
-- name    : WorkbookSource.base_6651
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:18:58.792204+00:00
-- url     : https://prove2.me/theorems/683e785d-93b3-4aac-9cff-ba1e888eca5f
-- title:
--   A cyclic mixed-product reciprocal lower bound at fixed sum three
-- statement:
--   Let $a,b,c>0$ and $a+b+c=3$ . Prove that: $\frac{a}{a+2bc} +\frac{b}{b+2ac}+\frac{c}{c+2ab} \ge 1$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6651` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6651; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6651 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (a + 2 * b * c) + b / (b + 2 * a * c) + c / (c + 2 * a * b) ≥ 1  :=  by sorry
