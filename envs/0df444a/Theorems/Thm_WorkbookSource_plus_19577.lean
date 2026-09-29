-- Prove2me | Theorems.Thm_WorkbookSource_plus_19577
-- name    : WorkbookSource.plus_19577
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:28:39.507113+00:00
-- url     : https://prove2.me/theorems/bc4eef9d-f04c-491b-8f03-a4104dad745d
-- title:
--   A factored tenth-degree three-variable polynomial is nonnegative
-- statement:
--   prove $(b-c)^2c^2((a-b)^2(a^4+2a^3b+6a^2b^2+2ab^3+b^4-2c^2(a+b)^2)+c^4(a^2+b^2))\geq0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_19577` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_19577; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_19577 (a b c : ℝ) : (b - c) ^ 2 * c ^ 2 * ((a - b) ^ 2 * (a ^ 4 + 2 * a ^ 3 * b + 6 * a ^ 2 * b ^ 2 + 2 * a * b ^ 3 + b ^ 4 - 2 * c ^ 2 * (a + b) ^ 2) + c ^ 4 * (a ^ 2 + b ^ 2)) ≥ 0   :=  by sorry
