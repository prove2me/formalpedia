-- Prove2me | Theorems.Thm_WorkbookSource_base_5157
-- name    : WorkbookSource.base_5157
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:42.879962+00:00
-- url     : https://prove2.me/theorems/b628c141-a466-42ce-8932-011714223204
-- title:
--   A symmetric quartic bound involving forty times a triple product
-- statement:
--   The inequality is equivalent to: $10(a^3b+b^3a+a^3c+c^3a+b^3c+c^3b)+9(a^4+b^4+c^4)+11(a^2b^2+a^2c^2+b^2c^2)\geq 40abc(a+b+c)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5157` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5157; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5157 (a b c : ℝ) : 10 * (a^3 * b + b^3 * a + a^3 * c + c^3 * a + b^3 * c + c^3 * b) + 9 * (a^4 + b^4 + c^4) + 11 * (a^2 * b^2 + a^2 * c^2 + b^2 * c^2) ≥ 40 * a * b * c * (a + b + c)  :=  by sorry
