-- Prove2me | Theorems.Thm_lean_workbook_plus_45619
-- name    : lean_workbook_plus_45619
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/cb87e224-de41-434f-8673-22b150433be6
-- statement:
--   Let $a,b\ge 0.$ Prove that \n $$ a+b+\frac{25}{4(a^2+ab+b+1)} \geq \frac{13}{4} $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45619 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a + b + 25 / (4 * (a ^ 2 + a * b + b + 1)) ≥ 13 / 4   :=  by sorry
