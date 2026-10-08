-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_39385
-- name    : WorkbookCorrected.plus_39385
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-06T20:55:33.448556+00:00
-- url     : https://prove2.me/theorems/2ca49d3c-34ae-48ac-809f-2ca27b7c981a
-- title:
--   Factorial arithmetic identity #39385
-- statement:
--   The elementary natural-number identity
--   $$
--   8! / (2! * 2! * 2! * 2!) = 2520
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_39385`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`, and whose stated right-hand side did not match the evaluated left-hand side. The repaired statement keeps the combinatorial/arithmetic left-hand side and uses the evaluated integer right-hand side (original RHS was 90).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_39385 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_39385; Apache-2.0; corrects Open node 96206349-3139-41be-9ea7-d10e8d549490

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_39385 : (Nat.factorial 8) / ((Nat.factorial 2) * (Nat.factorial 2) * (Nat.factorial 2) * (Nat.factorial 2)) = 2520 := by sorry
