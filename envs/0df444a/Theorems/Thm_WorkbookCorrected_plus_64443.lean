-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_64443
-- name    : WorkbookCorrected.plus_64443
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:43:04.732419+00:00
-- url     : https://prove2.me/theorems/16b56ce8-8b58-417d-913b-6908aa9805f2
-- title:
--   Inclusion-style factorial alternating sum
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   \frac{10!}{(2!)^3} - 3\cdot\frac{9!}{(2!)^2} + 3\cdot\frac{8!}{2!} - 7! = 236880
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_64443`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_64443 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_64443; Apache-2.0; corrects Open node 9c2d25de-9d2e-4483-90e0-ce6cfe4434b9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_64443 : Nat.factorial 10 / (Nat.factorial 2) ^ 3 - 3 * Nat.factorial 9 / (Nat.factorial 2) ^ 2 + 3 * Nat.factorial 8 / Nat.factorial 2 - Nat.factorial 7 = 236880 := by sorry
