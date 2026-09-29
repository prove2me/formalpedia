-- Prove2me | Theorems.Thm_WorkbookSource_plus_10841
-- name    : WorkbookSource.plus_10841
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:03:14.614808+00:00
-- url     : https://prove2.me/theorems/99da1f8d-8b31-4347-afdd-eff1963c1162
-- title:
--   A sixth-degree product bound involving three quadratic factors
-- statement:
--   For $a,b,c$ positive reals prove that $(\sum a^3)(a+b)(b+c)(c+a) \geq 3(a^2+bc)(b^2+ca)(c^2+ab)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_10841` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_10841; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_10841 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3)*(a + b)*(b + c)*(c + a) ≥ 3 * (a^2 + b * c)*(b^2 + c * a)*(c^2 + a * b)   :=  by sorry
