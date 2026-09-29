-- Prove2me | Theorems.Thm_lean_workbook_plus_79030
-- name    : lean_workbook_plus_79030
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/317cc175-79c7-4a9a-b4ec-4ab31a0faf81
-- statement:
--   Let $a$ be a real number such that $a^4+a^3=1$. Prove that $2a+3 >0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79030 (a : ℝ) (ha : a^4 + a^3 = 1) : 2 * a + 3 > 0   :=  by sorry
