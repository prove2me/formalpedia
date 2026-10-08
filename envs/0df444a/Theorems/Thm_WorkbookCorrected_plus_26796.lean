-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_26796
-- name    : WorkbookCorrected.plus_26796
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-06T20:55:45.607297+00:00
-- url     : https://prove2.me/theorems/1a852cef-c5c3-4d88-8f14-c7d7596a243b
-- title:
--   Binomial coefficient identity #26796
-- statement:
--   The elementary natural-number identity
--   $$
--   (\binom{12}{5}) - (\binom{10}{3}) = 672
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_26796`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`, and whose stated right-hand side did not match the evaluated left-hand side. The repaired statement keeps the combinatorial/arithmetic left-hand side and uses the evaluated integer right-hand side (original RHS was 564).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_26796 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_26796; Apache-2.0; corrects Open node a248188d-196b-447e-813e-60d83738e93b

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_26796 : ((Nat.choose 12 5)) - ((Nat.choose 10 3)) = 672 := by sorry
