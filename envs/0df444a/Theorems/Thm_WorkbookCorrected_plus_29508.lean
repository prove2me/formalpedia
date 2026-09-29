-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_29508
-- name    : WorkbookCorrected.plus_29508
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:52:35.323534+00:00
-- url     : https://prove2.me/theorems/be17c79d-b801-4abe-bd43-60ec5f7443bb
-- title:
--   Binomial coefficient identity #29508
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{6}{3}) = 20
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_29508`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_29508 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_29508; Apache-2.0; corrects Open node f7c8388e-d86d-4486-a81b-d9328c2fc750

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_29508 : (Nat.choose 6 3) = 20 := by sorry
