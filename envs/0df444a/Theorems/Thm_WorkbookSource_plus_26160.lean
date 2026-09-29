-- Prove2me | Theorems.Thm_WorkbookSource_plus_26160
-- name    : WorkbookSource.plus_26160
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:02:55.273234+00:00
-- url     : https://prove2.me/theorems/bbe3a4e0-9df2-4e80-a2c3-cc79f11442fe
-- title:
--   A rational inequality with a sum-product constraint
-- statement:
--   Let $a,b$ be positive real numbers such that $a+b+ab=1$ . Prove that $\frac{1+b^2}{1+a^2}\ge 2b.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_26160` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_26160; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.plus_26160 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b + a * b = 1) : (1 + b ^ 2) / (1 + a ^ 2) ≥ 2 * b   :=  by sorry
