-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_70458
-- name    : WorkbookCorrected.plus_70458
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:18:35.303602+00:00
-- url     : https://prove2.me/theorems/f1b4158b-c7f9-418a-a4c8-ba231b45ff82
-- title:
--   Seven factorial over three factorial squared equals 140
-- statement:
--   The quotient $\dfrac{7!}{3!\,3!}$ equals $140$, counting distinct arrangements of seven letters with two triples of repeats.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_70458`, which omitted the colon after the theorem name, used bare factorial notation under a preamble of only `Mathlib.Analysis.Complex.Basic`, and lacked the factorial imports.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_70458 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_70458; Apache-2.0; corrects Open node 44461a28-2ff0-4a29-8794-b663ef4587f0

import Mathlib.Data.Nat.Factorial.Basic

theorem WorkbookCorrected.plus_70458 : Nat.factorial 7 / (Nat.factorial 3 * Nat.factorial 3) = 140 := by sorry
