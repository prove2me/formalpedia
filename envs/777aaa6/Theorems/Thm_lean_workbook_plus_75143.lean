-- Prove2me | Theorems.Thm_lean_workbook_plus_75143
-- name    : lean_workbook_plus_75143
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/215b0393-2a2f-4ccf-8b8a-ed3f04a6c0ea
-- statement:
--   Prove that $b_n = \\frac{n(n+1)}{2} + 1 = \\frac{n^2+n+2}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75143 (n : ℕ) : n * (n + 1) / 2 + 1 = (n ^ 2 + n + 2) / 2   :=  by sorry
