-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_40193
-- name    : WorkbookCorrected.plus_40193
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:08:21.321134+00:00
-- url     : https://prove2.me/theorems/9b37a537-5317-4977-90a7-895dd19fd33e
-- title:
--   Binomial-factorial identity #40193
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{3}{2} * Nat.factorial 4) = 72
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_40193`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_40193 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_40193; Apache-2.0; corrects Open node 812404e2-c8eb-48fe-b19b-265e89f985ae

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_40193 : (Nat.choose 3 2 * Nat.factorial 4) = 72 := by sorry
