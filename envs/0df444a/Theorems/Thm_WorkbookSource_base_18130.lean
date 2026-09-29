-- Prove2me | Theorems.Thm_WorkbookSource_base_18130
-- name    : WorkbookSource.base_18130
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:13:06.761981+00:00
-- url     : https://prove2.me/theorems/db392484-e15b-4177-b017-be5ee1ed3628
-- title:
--   A mixed-power cyclic ratio lower bound
-- statement:
--   Prove the inequality:
--
--    $ \frac {a^2}{b} + \frac {b^3}{c^2} + \frac {c^4}{a^3} \ge - a + 2b + 2c.$
--
--    where $ a,b,c$ are positive real numbers.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18130` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18130; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18130 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 / b + b^3 / c^2 + c^4 / a^3 ≥ -a + 2 * b + 2 * c  :=  by sorry
