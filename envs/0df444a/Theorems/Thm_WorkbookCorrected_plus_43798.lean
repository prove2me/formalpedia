-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_43798
-- name    : WorkbookCorrected.plus_43798
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:26:11.783884+00:00
-- url     : https://prove2.me/theorems/8f6ad3e2-caac-471c-80fe-a417b08703d4
-- title:
--   Binomial coefficient identity #43798
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{52}{4}) = 270725
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_43798`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_43798 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_43798; Apache-2.0; corrects Open node ebbc3d12-2a70-4d78-9cc4-f68de7d76a8e

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_43798 : (Nat.choose 52 4) = 270725 := by sorry
