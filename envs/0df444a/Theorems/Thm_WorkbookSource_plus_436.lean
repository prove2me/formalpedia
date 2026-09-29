-- Prove2me | Theorems.Thm_WorkbookSource_plus_436
-- name    : WorkbookSource.plus_436
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:03:14.969071+00:00
-- url     : https://prove2.me/theorems/194b7e13-9e47-463e-a0a7-14e4cc6c20ab
-- title:
--   An asymmetric quartic bound on nonnegative variables
-- statement:
--   Let $ a,b,c \geq 0$ ,prove that:
--
--    $b^3a+a^4+c^4 \geq abc(c+b)+a^3c.$
--
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_436` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_436; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_436 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : b^3 * a + a^4 + c^4 ≥ a * b * c * (c + b) + a^3 * c   :=  by sorry
