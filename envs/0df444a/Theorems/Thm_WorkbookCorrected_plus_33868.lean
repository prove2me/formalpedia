-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_33868
-- name    : WorkbookCorrected.plus_33868
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:26:25.824678+00:00
-- url     : https://prove2.me/theorems/7ad75aa1-8992-42d1-9cdd-d3df5ac28851
-- title:
--   Binomial-factorial identity #33868
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   \binom{200}{100} = 200! / (100! * 100!)
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_33868`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_33868 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_33868; Apache-2.0; corrects Open node f8a4a48c-607d-441e-a51f-ef24dbb793f2

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_33868 : (Nat.choose 200 100) = (Nat.factorial 200) / ((Nat.factorial 100) * (Nat.factorial 100)) := by sorry
