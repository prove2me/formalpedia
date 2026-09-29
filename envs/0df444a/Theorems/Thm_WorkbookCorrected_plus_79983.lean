-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_79983
-- name    : WorkbookCorrected.plus_79983
-- status  : Disproved
-- author  : @carlok
-- created : 2026-09-22T11:56:30.370188+00:00
-- url     : https://prove2.me/theorems/8a95a13e-32c7-4151-bb08-dd2ded3cf5b3
-- title:
--   Factorial arithmetic identity #79983
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   8! / (2!^4) = 90
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_79983`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_79983 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_79983; Apache-2.0; corrects Open node 7c1824f7-b6b1-4fa1-8fee-f4051b38d3c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_79983 : (Nat.factorial 8) / ((Nat.factorial 2)^4) = 90 := by sorry
