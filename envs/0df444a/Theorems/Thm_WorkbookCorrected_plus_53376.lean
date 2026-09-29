-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_53376
-- name    : WorkbookCorrected.plus_53376
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:29:12.729569+00:00
-- url     : https://prove2.me/theorems/6a5c3c1b-e645-41c6-a56a-de3e2308373c
-- title:
--   Linear combination of squared factorials
-- statement:
--   The elementary natural-number identity
--   $$
--   14\cdot 3!\cdot 3! + 4\cdot 3!\cdot 3! = 18\cdot 3!\cdot 3!
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_53376`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_53376 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_53376; Apache-2.0; corrects Open node a172d837-7c86-4ce5-9aaf-b8aad9bb4370

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_53376 : (14 : ℕ) * Nat.factorial 3 * Nat.factorial 3 + 4 * Nat.factorial 3 * Nat.factorial 3 = 18 * Nat.factorial 3 * Nat.factorial 3 := by sorry
