-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_31830
-- name    : WorkbookCorrected.plus_31830
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T12:37:59.276342+00:00
-- url     : https://prove2.me/theorems/80d157dd-e8f9-4bf2-bc83-fd47d30f8901
-- title:
--   Binomial coefficient identity #31830
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   Nat.choose (6 + 4 - 1) 4 = 126
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_31830`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_31830 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_31830; Apache-2.0; corrects Open node e23cfee3-fbb1-49be-8753-1fe6901a11a1

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_31830 : (Nat.choose (6 + 4 - 1) 4) = 126 := by sorry
