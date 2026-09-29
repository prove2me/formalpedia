-- Prove2me | Theorems.Thm_lean_workbook_plus_75400
-- name    : lean_workbook_plus_75400
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/196f7c97-17b3-4be0-884a-ceb02ed265d7
-- statement:
--   Prove that $\binom{n+1}{2}+n+1=\binom{n+2}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75400 (n : ℕ) : (n + 1).choose 2 + n + 1 = (n + 2).choose 2   :=  by sorry
