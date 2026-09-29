-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_66104
-- name    : WorkbookCorrected.plus_66104
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:14:28.007914+00:00
-- url     : https://prove2.me/theorems/a2a5a627-5166-4d96-bc67-2be4cbed9e69
-- title:
--   Cosine of pi over two is zero
-- statement:
--   The elementary identity $\cos(\pi/2)=0$.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_66104`, which used bare `cos`/`π` without opening `Real`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_66104 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_66104; Apache-2.0; corrects Open node 751acc21-0c52-4a82-8bc3-23fdb93c9a63

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

theorem WorkbookCorrected.plus_66104 : Real.cos (Real.pi / 2) = 0 := by sorry
