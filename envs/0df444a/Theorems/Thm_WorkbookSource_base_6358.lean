-- Prove2me | Theorems.Thm_WorkbookSource_base_6358
-- name    : WorkbookSource.base_6358
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:05:43.025305+00:00
-- url     : https://prove2.me/theorems/cd3022d8-9bb1-48ca-84f4-fe86ccbcfb23
-- title:
--   A fifth-power bound involving a triple product
-- statement:
--   Prove that for all real $a, b, c \geq 0$ , $(a+b+c)^5\geq81abc(a^2+b^2+c^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6358` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6358; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6358 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + b + c) ^ 5 ≥ 81 * a * b * c * (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
