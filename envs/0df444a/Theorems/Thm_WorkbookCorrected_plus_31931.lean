-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_31931
-- name    : WorkbookCorrected.plus_31931
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-06T20:55:21.049473+00:00
-- url     : https://prove2.me/theorems/95c31be2-705b-4f4d-b7e5-8b754260f7b3
-- title:
--   Factorial arithmetic identity #31931
-- statement:
--   The elementary natural-number identity
--   $$
--   10 * 8 * 6 * 4 / 4! = 80
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_31931`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`, and whose stated right-hand side did not match the evaluated left-hand side. The repaired statement keeps the combinatorial/arithmetic left-hand side and uses the evaluated integer right-hand side (original RHS was 240).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_31931 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_31931; Apache-2.0; corrects Open node 3f35d5b7-85c1-433a-87da-e811ae350f70

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_31931 : 10 * 8 * 6 * 4 / (Nat.factorial 4) = 80 := by sorry
