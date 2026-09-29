-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_49544
-- name    : WorkbookCorrected.plus_49544
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:52:43.994742+00:00
-- url     : https://prove2.me/theorems/167b07c7-c4ed-462d-97be-261cd171da31
-- title:
--   Binomial coefficient identity #49544
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{3}{1}) * (\binom{5}{2} + \binom{5}{3}) * (\binom{4}{2}) = 360
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_49544`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_49544 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_49544; Apache-2.0; corrects Open node b03d2709-3a22-4b1a-a93d-f1e58d71a8bd

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_49544 : (Nat.choose 3 1) * ((Nat.choose 5 2) + (Nat.choose 5 3)) * (Nat.choose 4 2) = 360 := by sorry
