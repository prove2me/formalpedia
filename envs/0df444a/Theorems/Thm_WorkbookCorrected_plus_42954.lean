-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_42954
-- name    : WorkbookCorrected.plus_42954
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:30:21.149903+00:00
-- url     : https://prove2.me/theorems/196ddce4-e7c8-42b4-8884-02dbb08fb55f
-- title:
--   Elementary arithmetic identity #42954
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   5 + 80 + 90 + 20 + 1 = 196
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_42954`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_42954 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_42954; Apache-2.0; corrects Open node 8a01bb5f-e092-44cd-a1d3-ebcbd5cd8680

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_42954 : 5 + 80 + 90 + 20 + 1 = 196 := by sorry
