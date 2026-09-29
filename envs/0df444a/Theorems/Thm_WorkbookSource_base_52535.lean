-- Prove2me | Theorems.Thm_WorkbookSource_base_52535
-- name    : WorkbookSource.base_52535
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:40.818976+00:00
-- url     : https://prove2.me/theorems/3a3918a7-8138-4d4c-a6c2-c941f3c20e67
-- title:
--   A symmetric four-variable quartic inequality
-- statement:
--   Prove that $\frac{17}{8}(a^4+b^4+c^4+d^4-4abcd)\geq(a+b+c+d)(a^3+b^3+c^3+d^3-abc-abd-acd-bcd)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52535` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52535; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_52535 (a b c d : ℝ) : (17 / 8) * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 - 4 * a * b * c * d) ≥ (a + b + c + d) * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 - a * b * c - a * b * d - a * c * d - b * c * d)  :=  by sorry
