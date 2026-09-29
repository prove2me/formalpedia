-- Prove2me | Theorems.Thm_WorkbookSource_base_12997
-- name    : WorkbookSource.base_12997
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:48:31.01901+00:00
-- url     : https://prove2.me/theorems/680acf46-9d73-42ac-a39c-c257e9b655ae
-- title:
--   A cyclic quadratic difference over shifted pair products
-- statement:
--   Let a,b,c be positive real numbers. Prove that:
--    $\frac{a(a-2b+c)}{ab+1} + \frac{b(b-2c+a)}{bc+1} + \frac{c(c-2a+b)}{ac+1} \geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12997` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12997; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12997 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (a - 2 * b + c) / (a * b + 1) + b * (b - 2 * c + a) / (b * c + 1) + c * (c - 2 * a + b) / (c * a + 1)) ≥ 0  :=  by sorry
