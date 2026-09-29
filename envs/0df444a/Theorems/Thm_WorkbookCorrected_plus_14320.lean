-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_14320
-- name    : WorkbookCorrected.plus_14320
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:14:25.912506+00:00
-- url     : https://prove2.me/theorems/79380aa4-0c6d-49b4-9657-0c46ee6a927d
-- title:
--   Tangent of pi over four is one
-- statement:
--   The elementary identity $\tan(\pi/4)=1$.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_14320`, which used bare `tan`/`π` without opening `Real`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_14320 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_14320; Apache-2.0; corrects Open node efe2da9c-9c31-4ada-9b63-acab4242113d

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

theorem WorkbookCorrected.plus_14320 : Real.tan (Real.pi / 4) = 1 := by sorry
