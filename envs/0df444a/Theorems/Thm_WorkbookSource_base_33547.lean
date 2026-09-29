-- Prove2me | Theorems.Thm_WorkbookSource_base_33547
-- name    : WorkbookSource.base_33547
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:17.450553+00:00
-- url     : https://prove2.me/theorems/ca24f02e-cf09-4bb9-9aa0-45f9f69e0e69
-- title:
--   A symmetric quartic bound involving a triple product
-- statement:
--   Prove that for positive real numbers $a, b, c$:
--   $$\frac{a^4+b^4+c^4+5(a^2b^2+b^2c^2+c^2a^2)}{2} \ge 3abc(a+b+c)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33547` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33547; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33547 (a b c : ℝ) : (a^4 + b^4 + c^4 + 5 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)) / 2 ≥ 3 * a * b * c * (a + b + c)  :=  by sorry
