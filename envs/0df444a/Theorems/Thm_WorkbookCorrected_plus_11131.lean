-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_11131
-- name    : WorkbookCorrected.plus_11131
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T19:19:06.510062+00:00
-- url     : https://prove2.me/theorems/e8882b56-97c0-4880-9aeb-8dcc1b0a7d5c
-- title:
--   Binomial coefficient identity #11131
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   286 * ((\binom{9}{6})) = 3 * ((\binom{16}{6}))
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_11131`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_11131 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_11131; Apache-2.0; corrects Open node f9fafd7e-d754-47c4-8ca5-62a2d05f0a37

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_11131 : (286:ℚ) * ((Nat.choose 9 6)) = (3:ℚ) * ((Nat.choose 16 6)) := by sorry
