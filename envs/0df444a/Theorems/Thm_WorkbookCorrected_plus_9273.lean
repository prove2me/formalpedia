-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_9273
-- name    : WorkbookCorrected.plus_9273
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-06T20:55:43.859702+00:00
-- url     : https://prove2.me/theorems/a2613ce5-d1f4-4704-80e8-358670bf32e8
-- title:
--   Binomial-factorial identity #9273
-- statement:
--   The elementary natural-number identity
--   $$
--   (\binom{8}{4} * 7! * 4!) = 8467200
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_9273`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`, and whose stated right-hand side did not match the evaluated left-hand side. The repaired statement keeps the combinatorial/arithmetic left-hand side and uses the evaluated integer right-hand side (original RHS was 90720).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_9273 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_9273; Apache-2.0; corrects Open node 6a7ac830-d8c4-48d1-abf2-9374c4e9a78d

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_9273 : ((Nat.choose 8 4) * (Nat.factorial 7) * (Nat.factorial 4)) = 8467200 := by sorry
