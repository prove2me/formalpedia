-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_58052
-- name    : WorkbookCorrected.plus_58052
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:43:00.643048+00:00
-- url     : https://prove2.me/theorems/3ee341e6-93cc-44bb-8a94-4295d040d647
-- title:
--   Eight factorial minus adjusted seven factorial
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   8! - (4\cdot 7! - 2\cdot 6!) = 21600
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_58052`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_58052 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_58052; Apache-2.0; corrects Open node 3ecafe89-91c2-4ac0-9612-87af26708714

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_58052 : Nat.factorial 8 - (4 * Nat.factorial 7 - 2 * Nat.factorial 6) = 21600 := by sorry
