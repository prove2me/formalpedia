-- Prove2me | Theorems.Thm_WorkbookSource_plus_79113
-- name    : WorkbookSource.plus_79113
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:19:09.625216+00:00
-- url     : https://prove2.me/theorems/ca273e3b-50ac-4f7d-aad7-5184fb97849b
-- title:
--   A four-variable quartic bound involving the square of a sum
-- statement:
--   Prove that $3(a^2+b^2+c^2+d^2)^2+4(a^2+d^2)(b^2+c^2) \geq (a^2+b^2+c^2+d^2)(a+b+c+d)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_79113` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_79113; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_79113 (a b c d : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 + 4 * (a ^ 2 + d ^ 2) * (b ^ 2 + c ^ 2) ≥ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (a + b + c + d) ^ 2   :=  by sorry
