-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_73773
-- name    : WorkbookCorrected.plus_73773
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:29:14.054312+00:00
-- url     : https://prove2.me/theorems/4110785b-22d0-49de-9fcf-18ae1a6119e2
-- title:
--   Six factorial over two factorial
-- statement:
--   The elementary natural-number identity
--   $$
--   \frac{6!}{2!}=\frac{720}{2}
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_73773`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_73773 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_73773; Apache-2.0; corrects Open node c5653899-63e8-47e8-a441-855472743758

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_73773 : Nat.factorial 6 / Nat.factorial 2 = 720 / 2 := by sorry
