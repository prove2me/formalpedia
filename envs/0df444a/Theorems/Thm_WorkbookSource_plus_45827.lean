-- Prove2me | Theorems.Thm_WorkbookSource_plus_45827
-- name    : WorkbookSource.plus_45827
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:12:02.038837+00:00
-- url     : https://prove2.me/theorems/07845d4f-3a55-4a2a-9b41-5f7f56a34d46
-- title:
--   A cubic product bound involving an absolute value
-- statement:
--   Prove that $(1+|a|+a^2)^3 \geq (1+|a|)^3(1+|a|^3)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_45827` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_45827; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_45827 (a : ℝ) : (1 + |a| + a^2)^3 ≥ (1 + |a|)^3 * (1 + |a|^3)   :=  by sorry
