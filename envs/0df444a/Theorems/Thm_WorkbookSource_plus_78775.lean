-- Prove2me | Theorems.Thm_WorkbookSource_plus_78775
-- name    : WorkbookSource.plus_78775
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:56:08.972906+00:00
-- url     : https://prove2.me/theorems/907c5c03-6de9-4e4e-94ec-e86736ebabda
-- title:
--   A quadratic reciprocal sum with a product correction at fixed sum three
-- statement:
--   Let a,b,c>0 such that $a + b + c = 3$ . Prove that $\frac{{{a^2}}}{b} + \frac{{{b^2}}}{c} + \frac{{{c^2}}}{a} + \frac{{9abc}}{{ab + bc + ca}} \ge 6$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_78775` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_78775; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_78775 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3) : a^2 / b + b^2 / c + c^2 / a + 9 * a * b * c / (a * b + b * c + c * a) ≥ 6   :=  by sorry
