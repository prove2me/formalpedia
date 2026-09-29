-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_79038
-- name    : WorkbookCorrected.plus_79038
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:42:56.542284+00:00
-- url     : https://prove2.me/theorems/98372b44-4920-465c-a3af-6ce2c2930302
-- title:
--   Six factorial over two squared factorials
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   \frac{6!}{2!\,2!} = 180
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_79038`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_79038 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_79038; Apache-2.0; corrects Open node 9ddddd81-b50d-45f8-8662-a1982e85862e

import Mathlib.Data.Nat.Factorial.Basic

theorem WorkbookCorrected.plus_79038 : Nat.factorial 6 / (Nat.factorial 2 * Nat.factorial 2) = 180 := by sorry
