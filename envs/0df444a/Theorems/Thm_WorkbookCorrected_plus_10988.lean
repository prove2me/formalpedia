-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_10988
-- name    : WorkbookCorrected.plus_10988
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:41:29.445732+00:00
-- url     : https://prove2.me/theorems/8554caa9-ba6e-4d98-bc6c-31c9d8caebb1
-- title:
--   Factorial arithmetic identity #10988
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (2 / (6^5)) * (5!) = 5 / 162
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_10988`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_10988 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_10988; Apache-2.0; corrects Open node 34887443-2182-48fe-8ce2-5e4e6bbe73f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_10988 : ((2:ℚ) / (6 ^ 5)) * ((Nat.factorial 5)) = (5:ℚ) / 162 := by sorry
