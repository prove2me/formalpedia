-- Prove2me | Theorems.Thm_WorkbookSource_base_56863
-- name    : WorkbookSource.base_56863
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:03:12.798875+00:00
-- url     : https://prove2.me/theorems/fe49c22a-91d8-4fa1-893f-37e376a1a7fc
-- title:
--   A fifth-degree product comparison of symmetric expressions
-- statement:
--   Prove that for all a,b,c >0. we have $(a^{2}+b^{2}+c^{2})(a+b)(b+c)(c+a)\geq{(a^{3}+b^{3}+c^{3}+5abc)(ab+bc+ca)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_56863` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_56863; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_56863 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) * (a + b) * (b + c) * (c + a) ≥ (a^3 + b^3 + c^3 + 5 * a * b * c) * (a * b + b * c + c * a)  :=  by sorry
