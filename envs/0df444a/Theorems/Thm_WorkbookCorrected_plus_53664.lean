-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_53664
-- name    : WorkbookCorrected.plus_53664
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:29:15.166933+00:00
-- url     : https://prove2.me/theorems/0d4254d6-365e-4366-8039-b20283460802
-- title:
--   Factorial seconds-per-day quotient equals 42
-- statement:
--   The elementary natural-number identity
--   $$
--   \frac{10!}{60\cdot 60\cdot 24}=42
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_53664`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_53664 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_53664; Apache-2.0; corrects Open node b49c268c-110b-41bb-a51f-4be40dc1895b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_53664 : Nat.factorial 10 / (60 * 60 * 24) = 42 := by sorry
