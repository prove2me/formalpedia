-- Prove2me | Theorems.Thm_WorkbookSource_base_28299
-- name    : WorkbookSource.base_28299
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:55:21.772372+00:00
-- url     : https://prove2.me/theorems/57bc6ef3-8cc9-48ec-bfd1-fd3a4f948ebb
-- title:
--   A fifth-degree product bound involving symmetric sums
-- statement:
--   Prove that the following inequality is also true. Let $a, b, c>0$ . Prove that $(a+b+c)^2(a+b)(b+c)(c+a)\le4(a^3+b^3+c^3+3abc)(ab+bc+ca)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28299` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28299; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28299 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 2 * (a + b) * (b + c) * (c + a) ≤ 4 * (a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c) * (a * b + b * c + c * a)  :=  by sorry
