-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_60880
-- name    : WorkbookCorrected.plus_60880
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:21:38.489098+00:00
-- url     : https://prove2.me/theorems/68fdb127-e84d-46b9-b0b5-cf9b9829adcf
-- title:
--   Binomial coefficient identity #60880
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{7}{2} * \binom{16}{1}) = 336
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_60880`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_60880 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_60880; Apache-2.0; corrects Open node 510efcd1-4220-45a7-96d7-b085a20a6aa2

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_60880 : (Nat.choose 7 2 * (Nat.choose 16 1)) = 336 := by sorry
