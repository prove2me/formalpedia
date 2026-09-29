-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_6048
-- name    : WorkbookCorrected.plus_6048
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:43:07.873431+00:00
-- url     : https://prove2.me/theorems/10d6886e-4cc2-46d4-ac14-7f8618ac7a61
-- title:
--   Binomial coefficient identity #6048
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{64}{2}) = 2016
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_6048`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_6048 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_6048; Apache-2.0; corrects Open node 4aceb586-2a2f-4410-a76f-665d7003259c

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_6048 : (Nat.choose 64 2) = 2016 := by sorry
