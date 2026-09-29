-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_60369
-- name    : WorkbookCorrected.plus_60369
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:28:47.812391+00:00
-- url     : https://prove2.me/theorems/4b3efbed-0295-4fcd-89f8-bcbcfbd674c3
-- title:
--   Four-term difference equals 496
-- statement:
--   The elementary natural-number identity
--   $$
--   1792 - 400 - 432 - 464 = 496
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_60369`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_60369 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_60369; Apache-2.0; corrects Open node d63b85fa-3540-4d2e-b010-7d801dcb00b8

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_60369 : (1792 : ℕ) - 400 - 432 - 464 = 496 := by sorry
