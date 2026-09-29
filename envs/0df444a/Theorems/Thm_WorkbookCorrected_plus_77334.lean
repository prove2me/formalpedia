-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_77334
-- name    : WorkbookCorrected.plus_77334
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:24:56.817053+00:00
-- url     : https://prove2.me/theorems/d01e9269-4c59-44c1-87d7-736967f8612a
-- title:
--   Euler totient of fifteen is eight
-- statement:
--   Euler's totient satisfies
--   $$
--   \varphi(15)=8.
--   $$
--   Equivalently, if $n=15$ then $\varphi(n)=8$.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_77334`, which used a preamble of only `Mathlib.Analysis.Complex.Basic` (and, where relevant, non-compiling notation such as bare `φ`).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_77334 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_77334; Apache-2.0; corrects Open node ce767a9d-3bfe-496d-8797-95a0d3fc1b7f

import Mathlib.Data.Nat.Totient

theorem WorkbookCorrected.plus_77334 (n : ℕ) (h : n = 15) : Nat.totient n = 8 := by sorry
