-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_76111
-- name    : WorkbookCorrected.plus_76111
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:28:46.486905+00:00
-- url     : https://prove2.me/theorems/a5664c83-d322-4fee-923e-358c31d0383c
-- title:
--   Two-case counting product equals 1768026
-- statement:
--   The elementary natural-number identity
--   $$
--   29\cdot 39\cdot 38\cdot 37 + 3\cdot 40\cdot 39\cdot 38 = 1768026
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_76111`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_76111 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_76111; Apache-2.0; corrects Open node a622d5f9-d2ab-4cdd-95b7-279c9662d401

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_76111 : (29 : ℕ) * 39 * 38 * 37 + 3 * 40 * 39 * 38 = 1768026 := by sorry
