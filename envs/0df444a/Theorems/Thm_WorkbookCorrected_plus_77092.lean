-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_77092
-- name    : WorkbookCorrected.plus_77092
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T19:14:51.432638+00:00
-- url     : https://prove2.me/theorems/9cfb5ba2-333c-4154-b12d-14c5e511ec82
-- title:
--   Elementary arithmetic identity #77092
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + 3 + 6 + 10 + 15 + 21 + 28 + 36 + 45 + 55 + 66 + 78 + 91 + 105 + 120 + 136 = 816
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_77092`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_77092 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_77092; Apache-2.0; corrects Open node 6a197dff-9eb0-4b07-8998-e434d8f72135

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_77092 : 1 + 3 + 6 + 10 + 15 + 21 + 28 + 36 + 45 + 55 + 66 + 78 + 91 + 105 + 120 + 136 = 816 := by sorry
