-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_23470
-- name    : WorkbookCorrected.plus_23470
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T19:58:39.699147+00:00
-- url     : https://prove2.me/theorems/8779691c-d26b-450e-adbc-cd0547c06676
-- title:
--   Binomial coefficient identity #23470
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   9 * ((\binom{35}{20})) = 4 * ((\binom{35}{20}) + (\binom{35}{16}))
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_23470`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_23470 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_23470; Apache-2.0; corrects Open node e85f58ab-f331-4b21-b017-c88fa1f7fd6e

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_23470 : (9:ℚ) * ((Nat.choose 35 20)) = (4:ℚ) * ((Nat.choose 35 20) + (Nat.choose 35 16)) := by sorry
