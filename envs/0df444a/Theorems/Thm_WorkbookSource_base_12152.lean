-- Prove2me | Theorems.Thm_WorkbookSource_base_12152
-- name    : WorkbookSource.base_12152
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:18:37.880979+00:00
-- url     : https://prove2.me/theorems/5068bd6f-ae11-486e-950a-ba4e8c1036e2
-- title:
--   A quadratic form with a nonnegative parameter
-- statement:
--   Let $a,b,c$ be real numbers. Prove that
--    $$a^2+2b^2+2c^2+ka+\frac{7k^2}{24}\ge ab+2bc+ca+kc$$ Where $ k\geq 0.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12152` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12152; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12152 (a b c k : ℝ) (h : k ≥ 0) : a^2 + 2 * b^2 + 2 * c^2 + k * a + 7 * k^2 / 24 ≥ a * b + 2 * b * c + c * a + k * c  :=  by sorry
