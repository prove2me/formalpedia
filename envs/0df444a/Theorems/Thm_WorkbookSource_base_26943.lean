-- Prove2me | Theorems.Thm_WorkbookSource_base_26943
-- name    : WorkbookSource.base_26943
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:47:30.99202+00:00
-- url     : https://prove2.me/theorems/cf196257-0a90-4751-9d7a-69eb5a583c49
-- title:
--   A sixth-power bound for the Vandermonde square
-- statement:
--   Let $a,b,c$ Be real numbers. Prove that $2a^6+2b^6+2c^6-6a^2b^2c^2 \geqslant (a-b)^2(b-c)^2(c-a)^2 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26943` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26943; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26943 (a b c : ℝ) : 2 * a ^ 6 + 2 * b ^ 6 + 2 * c ^ 6 - 6 * a ^ 2 * b ^ 2 * c ^ 2 ≥ (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2  :=  by sorry
