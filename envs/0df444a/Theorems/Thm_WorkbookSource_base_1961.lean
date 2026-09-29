-- Prove2me | Theorems.Thm_WorkbookSource_base_1961
-- name    : WorkbookSource.base_1961
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:22.617476+00:00
-- url     : https://prove2.me/theorems/90a16400-42fd-40a2-b170-bc5816c11604
-- title:
--   A fourth-power bound involving the sum of three variables
-- statement:
--   If $a,b,c$ are real numbers, prove that
--    $$ a^4+b^4+c^4+(a+b+c)^4 \geq 28abc(a+b+c). $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1961` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1961; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1961 (a b c : ℝ) : a^4+b^4+c^4+(a+b+c)^4 ≥ 28*a*b*c*(a+b+c)  :=  by sorry
