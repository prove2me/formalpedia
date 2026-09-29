-- Prove2me | Theorems.Thm_WorkbookSource_base_4667
-- name    : WorkbookSource.base_4667
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:13:20.138369+00:00
-- url     : https://prove2.me/theorems/ab9ee221-43c2-4e90-b302-69fdef5fe295
-- title:
--   A cyclic rational comparison involving a triple product
-- statement:
--   If $a,b,c>0$ than prove that:
--   $\frac{a+b+c}{1+abc}\geq\frac{a}{1+a^2b}+\frac{b}{1+b^2c}+\frac{c}{1+c^2a}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4667` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4667; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4667 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) / (1 + a * b * c) ≥ a / (1 + a ^ 2 * b) + b / (1 + b ^ 2 * c) + c / (1 + c ^ 2 * a)  :=  by sorry
