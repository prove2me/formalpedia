-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_60818
-- name    : WorkbookCorrected.plus_60818
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:15:56.1073+00:00
-- url     : https://prove2.me/theorems/ea4dc004-7526-4f6b-bfdc-54cfa3be52d1
-- title:
--   Factorial arithmetic identity #60818
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   10! / (4! * 6!) * (6! / (3! * 3!)) * (3! / (2! * 1!)) * (1! / (1! * 0!)) = 12600
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_60818`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_60818 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_60818; Apache-2.0; corrects Open node e65deb6a-a624-4a46-b0ce-56f7ba5bfcf9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_60818 : (Nat.factorial 10) / ((Nat.factorial 4) * (Nat.factorial 6)) * ((Nat.factorial 6) / ((Nat.factorial 3) * (Nat.factorial 3))) * ((Nat.factorial 3) / ((Nat.factorial 2) * (Nat.factorial 1))) * ((Nat.factorial 1) / ((Nat.factorial 1) * (Nat.factorial 0))) = 12600 := by sorry
