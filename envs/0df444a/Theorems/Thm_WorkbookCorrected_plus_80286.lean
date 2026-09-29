-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_80286
-- name    : WorkbookCorrected.plus_80286
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:24:53.355081+00:00
-- url     : https://prove2.me/theorems/5eda1aac-a0de-452e-b684-eded9df0ecd2
-- title:
--   Inclusion-exclusion count equals 1806
-- statement:
--   The elementary natural-number identity
--   $$
--   1\cdot 3^{7}-3\cdot 2^{7}+3\cdot 1^{7}=1806
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_80286`, which omitted the colon after the theorem name and used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_80286 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_80286; Apache-2.0; corrects Open node 30240041-91cd-46bc-952c-f9f3d32c441a

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_80286 : (1 : ℕ) * 3 ^ 7 - 3 * 2 ^ 7 + 3 * 1 ^ 7 = 1806 := by sorry
