-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_67980
-- name    : WorkbookCorrected.plus_67980
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:14:22.465368+00:00
-- url     : https://prove2.me/theorems/0a16cb74-9ed5-4855-9211-e74bea066ffc
-- title:
--   Factorial arrangement count 10080
-- statement:
--   The multinomial count $8!/(2!\cdot 2!)$ equals $10080$, counting distinct permutations of eight letters with two pairs of repeats.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_67980`, which used `!` notation unavailable under the Complex.Basic-only preamble.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_67980 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_67980; Apache-2.0; corrects Open node 0868771e-abe7-4fc8-8ed1-b741df9a5074

import Mathlib.Data.Nat.Factorial.Basic

theorem WorkbookCorrected.plus_67980 : Nat.factorial 8 / (Nat.factorial 2 * Nat.factorial 2) = 10080 := by sorry
