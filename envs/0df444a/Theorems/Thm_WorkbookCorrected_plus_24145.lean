-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_24145
-- name    : WorkbookCorrected.plus_24145
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:43:02.549013+00:00
-- url     : https://prove2.me/theorems/c488370f-a999-49ed-bc61-5310f948a75d
-- title:
--   Factorial arithmetic identity #24145
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (7!)/(2!*2!) = 1260
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_24145`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_24145 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_24145; Apache-2.0; corrects Open node 4d785078-3bb5-4f2b-99cd-0d702f4bee94

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_24145 : (Nat.factorial 7)/((Nat.factorial 2)*(Nat.factorial 2)) = 1260 := by sorry
