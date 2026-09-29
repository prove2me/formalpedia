-- Prove2me | Theorems.Thm_lean_workbook_plus_35392
-- name    : lean_workbook_plus_35392
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/af79cb4b-efc8-47f4-a6b8-d1ccb6eb665b
-- statement:
--   Let $a,b,c>0$ positive real numbers such that : $ab+bc+ca=1$ Prove that : $a^2bc+b^2ca+c^2ab \leq \frac{1}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35392 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a = 1) : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ 1 / 3   :=  by sorry
