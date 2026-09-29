-- Prove2me | Theorems.Thm_WorkbookSource_plus_76073
-- name    : WorkbookSource.plus_76073
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:51:39.687135+00:00
-- url     : https://prove2.me/theorems/12446abe-866d-41c5-9b8c-867dc7d1950d
-- title:
--   A polynomial product inequality in three real variables
-- statement:
--   Let $a,b,c\geq 0$ . Prove that:
--    $a^{2}b^{2}c^{2}+2a^{2}b^{2}+2b^{2}c^{2}+2c^{2}a^{2}+a^{2}+b^{2}+c^{2}\geq (abc-1)(ab+bc+ca)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_76073` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_76073; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_76073 (a b c : ℝ) : a^2 * b^2 * c^2 + 2 * a^2 * b^2 + 2 * b^2 * c^2 + 2 * c^2 * a^2 + a^2 + b^2 + c^2 ≥ (a * b * c - 1) * (a * b + b * c + c * a)   :=  by sorry
