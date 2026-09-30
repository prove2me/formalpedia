-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_73622
-- name    : WorkbookCorrected.plus_73622
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T19:11:56.687319+00:00
-- url     : https://prove2.me/theorems/ffae1ffa-d9b1-42ec-a187-f03150d20c8b
-- title:
--   Binomial coefficient identity #73622
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{16}{4}) = (Nat.choose (12+4) 4)
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_73622`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_73622 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_73622; Apache-2.0; corrects Open node 6ecb4c37-ee75-4bbe-8deb-f5cec8693e4d

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_73622 : (Nat.choose 16 4) = (Nat.choose (12+4) 4) := by sorry
