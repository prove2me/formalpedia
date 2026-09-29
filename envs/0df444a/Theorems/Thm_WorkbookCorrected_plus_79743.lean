-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_79743
-- name    : WorkbookCorrected.plus_79743
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:18:29.869086+00:00
-- url     : https://prove2.me/theorems/64dc8723-846a-44d7-85f1-55bcd52ef485
-- title:
--   Six to the tenth equals two to the tenth times three to the tenth
-- statement:
--   Since $6=2\cdot 3$, raising both sides to the tenth power gives the multiplicative identity $6^{10}=2^{10}\cdot 3^{10}$ in the natural numbers.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_79743`, which omitted the colon after the theorem name and used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_79743 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_79743; Apache-2.0; corrects Open node 76f8518e-a0f7-4dca-946d-91e99cbdb3fb

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_79743 : (6 : ℕ) ^ 10 = 2 ^ 10 * 3 ^ 10 := by sorry
