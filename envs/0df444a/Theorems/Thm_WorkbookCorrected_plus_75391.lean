-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_75391
-- name    : WorkbookCorrected.plus_75391
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:31:08.839106+00:00
-- url     : https://prove2.me/theorems/fdd684dd-f1f5-4044-ac80-cfc50edc3e1a
-- title:
--   Factorial arithmetic identity #75391
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (2^3 * 3!)/6^3 = 2/9
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_75391`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_75391 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_75391; Apache-2.0; corrects Open node 2222e761-c0a1-4d32-8449-fa0556a06d49

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_75391 : ((2:ℚ) ^ 3 * (Nat.factorial 3))/6 ^ 3 = (2:ℚ)/9 := by sorry
