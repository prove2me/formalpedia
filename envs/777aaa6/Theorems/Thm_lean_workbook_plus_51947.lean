-- Prove2me | Theorems.Thm_lean_workbook_plus_51947
-- name    : lean_workbook_plus_51947
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/5e193f7b-3dbe-4f9c-b432-0bcbb155df7e
-- statement:
--   Prove that if a,b,c>0 then $\frac{b+c}{a+2b+2c}+\frac{c+a}{b+2c+2a}+\frac{a+b}{c+2a+2b}\leq \frac{6}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51947 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / (a + 2 * b + 2 * c) + (c + a) / (b + 2 * c + 2 * a) + (a + b) / (c + 2 * a + 2 * b) ≤ 6 / 5   :=  by sorry
