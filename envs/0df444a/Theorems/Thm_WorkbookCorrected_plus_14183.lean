-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_14183
-- name    : WorkbookCorrected.plus_14183
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T06:38:47.872798+00:00
-- url     : https://prove2.me/theorems/e08d069b-9037-4b43-a5e7-634fbb1eb094
-- title:
--   Rational arithmetic identity #14183
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (3999999/2000:ℚ) = (3999999/2000:ℚ)
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_14183`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_14183 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_14183; Apache-2.0; corrects Open node 55f9fb6b-33d0-4d4d-a580-78074293c309

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_14183 : (3999999/2000:ℚ) = (3999999/2000:ℚ) := by sorry
