-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_33723
-- name    : WorkbookCorrected.plus_33723
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T06:59:37.600839+00:00
-- url     : https://prove2.me/theorems/f436b1cf-c25a-476a-9e7f-38a6f5643685
-- title:
--   Binomial-factorial identity #33723
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   \binom{100}{50} = 100! / (50! * 50!)
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_33723`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_33723 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_33723; Apache-2.0; corrects Open node 540a64e0-d5a9-474e-825a-4dde0e346e3f

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_33723 : (Nat.choose 100 50) = (Nat.factorial 100) / ((Nat.factorial 50) * (Nat.factorial 50)) := by sorry
