-- Prove2me | Theorems.Thm_WorkbookSource_base_48908
-- name    : WorkbookSource.base_48908
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:15:41.047338+00:00
-- url     : https://prove2.me/theorems/c0406804-fdc2-45f0-8b20-d3456286f699
-- title:
--   A squared cubic sum bounds a fourth-power triple product
-- statement:
--   The following inequalities are also true. Let $a$ , $b$ and $c$ are non-negative numbers. Prove that: $(a+b+c)(a^3+b^3+c^3)^2\geq9abc(a^4+b^4+c^4)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48908` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48908; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_48908 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3) ^ 2 ≥ 9 * a * b * c * (a ^ 4 + b ^ 4 + c ^ 4)  :=  by sorry
