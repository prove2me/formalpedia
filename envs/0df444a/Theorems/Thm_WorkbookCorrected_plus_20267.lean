-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_20267
-- name    : WorkbookCorrected.plus_20267
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T09:53:30.692741+00:00
-- url     : https://prove2.me/theorems/07cd9957-3c65-4b38-b0e6-bf27f55f17d1
-- title:
--   Elementary inequality #20267
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (2^64) ≤ 64!
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_20267`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_20267 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_20267; Apache-2.0; corrects Open node bd6178b1-1eba-4518-98d9-2f4a625a97c8

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_20267 : (2 ^ 64) ≤ (Nat.factorial 64) := by sorry
