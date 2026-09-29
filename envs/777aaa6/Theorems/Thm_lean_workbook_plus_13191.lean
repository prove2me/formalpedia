-- Prove2me | Theorems.Thm_lean_workbook_plus_13191
-- name    : lean_workbook_plus_13191
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/ab8ed567-f643-4957-b953-cd244feb9858
-- statement:
--   Let $a,b,c\ge 0$ and $a^3+2b^3+2c^3=a+2b+2c$ . Prove that \n $$a^2+2b^2+2c^2\leq 5$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13191 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (ha3 : a^3 + 2 * b^3 + 2 * c^3 = a + 2 * b + 2 * c) : a^2 + 2 * b^2 + 2 * c^2 ≤ 5   :=  by sorry
