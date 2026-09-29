-- Prove2me | Theorems.Thm_WorkbookSource_base_1076
-- name    : WorkbookSource.base_1076
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:37.493181+00:00
-- url     : https://prove2.me/theorems/ec863a51-f8d0-425a-9518-bf302d9cdf46
-- title:
--   A four-variable quartic bound for two pairwise sums
-- statement:
--   Note that for any reals $a, b, c, d$ we have $(a^2+b^2+c^2+d^2)^2+16abcd\geq 2(a+c)^2(b+d)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1076` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1076; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1076 (a b c d : ℝ) : (a^2+b^2+c^2+d^2)^2+16*a*b*c*d ≥ 2*(a+c)^2*(b+d)^2  :=  by sorry
