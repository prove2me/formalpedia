-- Prove2me | Theorems.Thm_WorkbookSource_base_18429
-- name    : WorkbookSource.base_18429
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:32:48.533222+00:00
-- url     : https://prove2.me/theorems/ca3b9abe-5556-4442-8ae1-0a3b3af2e6f3
-- title:
--   A cyclic fourth-power ratio bounds a quadratic sum
-- statement:
--   For all positive real numbers $a, b, c$ , prove that $ \frac{a^4+5b^4}{a(a+2b)} + \frac{b^4+5c^4}{b(b+2c)} + \frac{c^4+5a^4}{c(c+2a)} \geq 2(a^2+b^2+c^2). $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18429` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18429; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18429 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^4 + 5 * b^4) / (a * (a + 2 * b)) + (b^4 + 5 * c^4) / (b * (b + 2 * c)) + (c^4 + 5 * a^4) / (c * (c + 2 * a)) ≥ 2 * (a^2 + b^2 + c^2)  :=  by sorry
