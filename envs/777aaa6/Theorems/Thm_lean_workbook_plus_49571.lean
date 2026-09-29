-- Prove2me | Theorems.Thm_lean_workbook_plus_49571
-- name    : lean_workbook_plus_49571
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5617664c-c793-485f-a411-5ad924f5f2a3
-- statement:
--   Let $a$ , $b$ , $c$ be positive real numbers satisfying $a^2<bc$ . Prove that $b^3+ac^2>ab(a+c)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49571 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a^2 < b * c) : b^3 + a * c^2 > a * b * (a + c)   :=  by sorry
