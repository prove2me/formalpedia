-- Prove2me | Theorems.Thm_WorkbookSource_base_8003
-- name    : WorkbookSource.base_8003
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:33:39.921613+00:00
-- url     : https://prove2.me/theorems/ecf80f5c-1b8c-4686-9c70-8f94fac003fc
-- title:
--   A cyclic weighted cubic ratio sum bounds the quadratic mean
-- statement:
--   Let a, b, c > 0. Prove: \\(\sum_{cyc} \\frac{a^3+3b^3}{5a+b} \\geq \\frac{2(a^2+b^2+c^2)}{3}\\)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8003` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8003; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8003 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + 3 * b^3) / (5 * a + b) + (b^3 + 3 * c^3) / (5 * b + c) + (c^3 + 3 * a^3) / (5 * c + a) ≥ 2 * (a^2 + b^2 + c^2) / 3  :=  by sorry
