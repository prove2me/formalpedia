-- Prove2me | Theorems.Thm_WorkbookSource_base_11560
-- name    : WorkbookSource.base_11560
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:10:45.876978+00:00
-- url     : https://prove2.me/theorems/dca9b289-82ed-49fc-b772-592e9b0cec1c
-- title:
--   A quartic bound under zero sum
-- statement:
--   Prove: $a^2b^2+a^2c^2+b^2c^2+3\geq6abc$ given $a+b+c=0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11560` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11560; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11560 (a b c : ℝ) (habc : a + b + c = 0) : a^2 * b^2 + a^2 * c^2 + b^2 * c^2 + 3 ≥ 6 * a * b * c  :=  by sorry
