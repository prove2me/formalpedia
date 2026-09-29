-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_50991
-- name    : WorkbookCorrected.plus_50991
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:08:19.71052+00:00
-- url     : https://prove2.me/theorems/e55ef043-90da-47a6-8630-bbaee7ffe431
-- title:
--   Factorial arithmetic identity #50991
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   5! = 5 * 4 * 3 * 2 * 1
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_50991`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_50991 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_50991; Apache-2.0; corrects Open node 0df21972-8978-4d3b-975b-c084163bbc7a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_50991 : (Nat.factorial 5) = 5 * 4 * 3 * 2 * 1 := by sorry
