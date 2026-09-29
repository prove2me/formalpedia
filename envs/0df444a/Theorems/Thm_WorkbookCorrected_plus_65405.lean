-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_65405
-- name    : WorkbookCorrected.plus_65405
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:24:50.203454+00:00
-- url     : https://prove2.me/theorems/e7455ce8-c26a-44e8-9eb3-afd48fb9b9c4
-- title:
--   Eight squared times ten to the eight
-- statement:
--   The elementary natural-number identity
--   $$
--   8^{2}\cdot 10^{8}=6400000000
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_65405`, which omitted the colon after the theorem name and used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_65405 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_65405; Apache-2.0; corrects Open node 78a7f913-ea1c-46a4-86a9-6e9945306426

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_65405 : (8 : ℕ) ^ 2 * 10 ^ 8 = 6400000000 := by sorry
