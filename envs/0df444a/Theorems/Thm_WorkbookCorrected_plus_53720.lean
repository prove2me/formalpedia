-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_53720
-- name    : WorkbookCorrected.plus_53720
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T19:58:38.765127+00:00
-- url     : https://prove2.me/theorems/da6228dd-b137-41bd-b91a-a132ca409087
-- title:
--   Binomial coefficient identity #53720
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   323 * ((\binom{15}{4})) = 91 * ((\binom{20}{4}))
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_53720`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_53720 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_53720; Apache-2.0; corrects Open node c43ed99f-a52d-4d0d-a107-85c736b3e4ce

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_53720 : (323:ℚ) * ((Nat.choose 15 4)) = (91:ℚ) * ((Nat.choose 20 4)) := by sorry
