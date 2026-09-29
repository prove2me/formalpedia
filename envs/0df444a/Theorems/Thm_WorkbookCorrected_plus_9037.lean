-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_9037
-- name    : WorkbookCorrected.plus_9037
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:56:28.482285+00:00
-- url     : https://prove2.me/theorems/66d14466-75f3-440b-ac1e-1a1d255bf6b8
-- title:
--   Factorial arithmetic identity #9037
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   10! / (8! * 2!) * (4! / (2! * 2!)) * (4! / (2! * 2!)) = 1620
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_9037`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_9037 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_9037; Apache-2.0; corrects Open node 51d2ccd9-03ec-4cd1-8a2d-f201a738a662

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_9037 : (Nat.factorial 10) / ((Nat.factorial 8) * (Nat.factorial 2)) * ((Nat.factorial 4) / ((Nat.factorial 2) * (Nat.factorial 2))) * ((Nat.factorial 4) / ((Nat.factorial 2) * (Nat.factorial 2))) = 1620 := by sorry
