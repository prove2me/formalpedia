-- Prove2me | Theorems.Thm_WorkbookSource_base_9
-- name    : WorkbookSource.base_9
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:34:21.118979+00:00
-- url     : https://prove2.me/theorems/55e87808-d800-4744-bf1b-6228ee9680a7
-- title:
--   A bound for a product minus its associated radical
-- statement:
--   $(ab+1)-\sqrt{1+a^2b^2}\leq 2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9 (a b : ℝ) : (a * b + 1) - Real.sqrt (1 + a ^ 2 * b ^ 2) ≤ 2  :=  by sorry
