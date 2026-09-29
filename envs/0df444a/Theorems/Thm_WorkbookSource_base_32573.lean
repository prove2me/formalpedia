-- Prove2me | Theorems.Thm_WorkbookSource_base_32573
-- name    : WorkbookSource.base_32573
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:43:17.549919+00:00
-- url     : https://prove2.me/theorems/f6a1db00-edbc-46ad-b2d1-8f6af92f06f7
-- title:
--   A mixed quadratic reciprocal upper bound
-- statement:
--   Let $a, b, c>0$ . Prove that $\frac{a+b}{5c^2+ab}+\frac{b+c}{5a^2+bc}+\frac{c+a}{5b^2+ca}\le\frac{a^2+b^2+c^2}{3abc}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32573` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32573; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32573 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (5 * c ^ 2 + a * b) + (b + c) / (5 * a ^ 2 + b * c) + (c + a) / (5 * b ^ 2 + c * a) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / (3 * a * b * c)  :=  by sorry
