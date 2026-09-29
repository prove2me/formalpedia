-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_76266
-- name    : WorkbookCorrected.plus_76266
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:24:53.693977+00:00
-- url     : https://prove2.me/theorems/5ca4bf24-82bf-4879-9029-ff4b62f83992
-- title:
--   Binomial four choose two minus two
-- statement:
--   The elementary binomial identity
--   $$
--   \binom{4}{2}-2=4
--   $$
--   holds in the natural numbers.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_76266`, which used a preamble of only `Mathlib.Analysis.Complex.Basic` (and, where relevant, non-compiling notation such as bare `φ`).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_76266 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_76266; Apache-2.0; corrects Open node e33523df-ed24-4b96-957a-00e8858a4057

import Mathlib.Data.Nat.Choose.Basic

theorem WorkbookCorrected.plus_76266 : Nat.choose 4 2 - 2 = 4 := by sorry
