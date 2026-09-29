-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_72890
-- name    : WorkbookCorrected.plus_72890
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:14:24.643115+00:00
-- url     : https://prove2.me/theorems/3806e25a-5985-41dd-8a43-60f2f5f469f6
-- title:
--   Fifteen factorial congruent to 0 mod 1000
-- statement:
--   The factorial $15!$ is divisible by $1000$, so $15! \equiv 0 \pmod{1000}$.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_72890`, which used `!`/`%` under an inadequate Complex.Basic-only preamble.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_72890 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_72890; Apache-2.0; corrects Open node 9a2d6cba-e7fa-4c1b-888b-12ba07253159

import Mathlib.Data.Nat.Factorial.Basic

theorem WorkbookCorrected.plus_72890 : Nat.factorial 15 % 1000 = 0 := by sorry
