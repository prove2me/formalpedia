-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_39224
-- name    : WorkbookCorrected.plus_39224
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:43:08.871202+00:00
-- url     : https://prove2.me/theorems/3f6c5b9f-ab61-4975-bdc7-20dd33075d72
-- title:
--   Elementary arithmetic identity #39224
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   2  *  81 = 162
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_39224`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_39224 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_39224; Apache-2.0; corrects Open node 4a90de74-2333-41a3-9173-4d6869566e7f

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_39224 : 2 * 81 = 162 := by sorry
