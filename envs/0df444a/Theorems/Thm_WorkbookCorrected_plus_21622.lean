-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_21622
-- name    : WorkbookCorrected.plus_21622
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:22:25.167449+00:00
-- url     : https://prove2.me/theorems/6b4c54b7-5af1-4551-b16d-f1d620ff6ec7
-- title:
--   Elementary arithmetic identity #21622
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   10 = 5 + 5 ∧ 11 = 5 + 6 ∧ 12 = 6 + 6 ∧ 13 = 5 + 6 + 2 ∧ 14 = 5 + 5 + 2 + 2
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_21622`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_21622 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_21622; Apache-2.0; corrects Open node 8ba47cb9-52d9-4506-a630-7c20c13b45f7

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_21622 : (10 = 5 + 5) ∧ (11 = 5 + 6) ∧ (12 = 6 + 6) ∧ (13 = 5 + 6 + 2) ∧ (14 = 5 + 5 + 2 + 2) := by sorry
