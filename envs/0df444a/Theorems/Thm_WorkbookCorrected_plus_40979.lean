-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_40979
-- name    : WorkbookCorrected.plus_40979
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:31:10.198175+00:00
-- url     : https://prove2.me/theorems/eb796a30-88b6-4a1c-bd15-ab056cbdbe2a
-- title:
--   Binomial coefficient identity #40979
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (3 * 5 * 4 + 3 * 5 * ( \binom{4}{2})) / (3^5) = 50 / 81
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_40979`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_40979 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_40979; Apache-2.0; corrects Open node 9c5714f5-e5ee-4f16-a1bd-2e385de65610

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_40979 : ((3:ℚ) * 5 * 4 + 3 * 5 * ( (Nat.choose 4 2))) / (3 ^ 5) = (50:ℚ) / 81 := by sorry
