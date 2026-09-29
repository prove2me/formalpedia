-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_73552
-- name    : WorkbookCorrected.plus_73552
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:18:33.166066+00:00
-- url     : https://prove2.me/theorems/055f94b9-a709-43d4-a99a-54092be1f2ca
-- title:
--   Multinomial ten over four three two one equals 12600
-- statement:
--   The multinomial coefficient $\dfrac{10!}{4!\,3!\,2!\,1!}$ equals $12600$.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_73552`, which omitted the colon after the theorem name, used bare factorial notation under a preamble of only `Mathlib.Analysis.Complex.Basic`, and lacked the factorial imports.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_73552 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_73552; Apache-2.0; corrects Open node 15f3a66b-72af-4dd7-a4fa-aba822ad2fa6

import Mathlib.Data.Nat.Factorial.Basic

theorem WorkbookCorrected.plus_73552 : Nat.factorial 10 / (Nat.factorial 4 * Nat.factorial 3 * Nat.factorial 2 * Nat.factorial 1) = 12600 := by sorry
