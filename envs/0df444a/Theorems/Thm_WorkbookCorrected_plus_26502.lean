-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_26502
-- name    : WorkbookCorrected.plus_26502
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:30:50.044457+00:00
-- url     : https://prove2.me/theorems/ed6db4e0-330e-4bc9-9242-f9b7df4c3c3e
-- title:
--   Rational arithmetic identity #26502
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (6*1 + 5*15 + 4*65 + 3*175 + 2*369 + 1*671)/1296 = 2275/1296
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_26502`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_26502 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_26502; Apache-2.0; corrects Open node e26acd10-2ca4-4e3e-b169-b24450199ccb

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_26502 : ((6:ℚ)*1 + 5*15 + 4*65 + 3*175 + 2*369 + 1*671)/1296 = (2275:ℚ)/1296 := by sorry
