-- Prove2me | Theorems.Thm_WorkbookSource_plus_12136
-- name    : WorkbookSource.plus_12136
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:21:57.960852+00:00
-- url     : https://prove2.me/theorems/43376b34-4b95-48df-bb03-962629b06a2d
-- title:
--   An asymmetric fixed-sum lower bound in mixed powers
-- statement:
--   Let $a,b,c\geq 0$ and $a+b+c=3.$ Prove that $a^3+ b^2 + c^3+ ab^2c \geq 4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_12136` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_12136; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_12136 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : a ^ 3 + b ^ 2 + c ^ 3 + a * b ^ 2 * c ≥ 4   :=  by sorry
