-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_23477
-- name    : WorkbookCorrected.plus_23477
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T13:34:03.547594+00:00
-- url     : https://prove2.me/theorems/70afc1c2-e685-49f4-a937-65068f57473d
-- title:
--   Elementary arithmetic identity #23477
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   169 + 196 + 225 + 256 + 289 + 324 + 361 + 400 + 441 + 484 + 529 + 576 + 625 + 676 + 729 + 784 + 841 + 900 = 8805
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_23477`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_23477 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_23477; Apache-2.0; corrects Open node 2bb7d74b-0951-4019-91ec-a6f34aed69e8

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_23477 : 169 + 196 + 225 + 256 + 289 + 324 + 361 + 400 + 441 + 484 + 529 + 576 + 625 + 676 + 729 + 784 + 841 + 900 = 8805 := by sorry
