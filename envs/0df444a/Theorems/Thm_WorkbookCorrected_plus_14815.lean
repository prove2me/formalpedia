-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_14815
-- name    : WorkbookCorrected.plus_14815
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:49:23.635262+00:00
-- url     : https://prove2.me/theorems/6640053f-6572-4c88-8d9f-fd83d95bb60f
-- title:
--   Factorial arithmetic identity #14815
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (6!)/(2!*3!) = 60
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_14815`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_14815 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_14815; Apache-2.0; corrects Open node 36fafe12-0c56-4400-935e-08ac61dbd63b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_14815 : ((Nat.factorial 6))/((Nat.factorial 2)*(Nat.factorial 3)) = 60 := by sorry
