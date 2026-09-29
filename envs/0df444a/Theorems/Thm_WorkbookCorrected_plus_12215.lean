-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_12215
-- name    : WorkbookCorrected.plus_12215
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:14:26.016304+00:00
-- url     : https://prove2.me/theorems/08406c01-77bd-46b8-8346-2c0bb8691662
-- title:
--   Sine of pi over two is one
-- statement:
--   The elementary identity $\sin(\pi/2)=1$.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_12215`, which used bare `sin`/`π` without opening `Real`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_12215 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_12215; Apache-2.0; corrects Open node 7138fec6-6e46-40bb-9b77-c863f23539b8

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

theorem WorkbookCorrected.plus_12215 : Real.sin (Real.pi / 2) = 1 := by sorry
