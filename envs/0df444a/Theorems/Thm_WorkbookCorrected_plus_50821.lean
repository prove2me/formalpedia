-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_50821
-- name    : WorkbookCorrected.plus_50821
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:17:43.237732+00:00
-- url     : https://prove2.me/theorems/f2c15651-30be-431a-8f18-2e8a99203681
-- title:
--   Binomial coefficient identity #50821
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   \binom{14}{5} = 2002
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_50821`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_50821 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_50821; Apache-2.0; corrects Open node 10c30b68-9550-407e-8630-62913fd6b045

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_50821 : (Nat.choose 14 5) = 2002 := by sorry
