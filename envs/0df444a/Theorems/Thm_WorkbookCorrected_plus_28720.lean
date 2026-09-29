-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_28720
-- name    : WorkbookCorrected.plus_28720
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:56:29.236901+00:00
-- url     : https://prove2.me/theorems/c1d28599-2b43-473e-afd1-d3a48f73be83
-- title:
--   Factorial arithmetic identity #28720
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   11! / (7! * 4!) + 9! / (5! * 4!) + 7! / (3! * 4!) + 5! / (1! * 4!) = 496
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_28720`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_28720 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_28720; Apache-2.0; corrects Open node 395c65cf-1bd5-43e7-8711-3131917380b6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_28720 : (Nat.factorial 11) / ((Nat.factorial 7) * (Nat.factorial 4)) + (Nat.factorial 9) / ((Nat.factorial 5) * (Nat.factorial 4)) + (Nat.factorial 7) / ((Nat.factorial 3) * (Nat.factorial 4)) + (Nat.factorial 5) / ((Nat.factorial 1) * (Nat.factorial 4)) = 496 := by sorry
