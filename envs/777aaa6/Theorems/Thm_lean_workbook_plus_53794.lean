-- Prove2me | Theorems.Thm_lean_workbook_plus_53794
-- name    : lean_workbook_plus_53794
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/872d7611-2412-4ff0-b821-7e1255311d75
-- statement:
--   Let $a,b,c\ge 0$ and $a^2+2b^2+2c^2=a^3+2b^3+2c^3$ . Prove that \n $$ a+2b+2c\leq 5 $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53794 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + 2 * b^2 + 2 * c^2 = a^3 + 2 * b^3 + 2 * c^3) : a + 2 * b + 2 * c ≤ 5   :=  by sorry
