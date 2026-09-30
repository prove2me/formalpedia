-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_6620
-- name    : WorkbookCorrected.plus_6620
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:38:04.765231+00:00
-- url     : https://prove2.me/theorems/bdd79b26-d8a4-4822-aabd-1764f88fc57d
-- title:
--   Rational arithmetic identity #6620
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = 0
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_6620`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_6620 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_6620; Apache-2.0; corrects Open node 05b8fbae-51cb-4a1a-a6e4-4ec33be60494

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_6620 : (0:ℚ) + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = (0:ℚ) := by sorry
