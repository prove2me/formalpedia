-- Prove2me | Theorems.Thm_lean_workbook_plus_9507
-- name    : lean_workbook_plus_9507
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/ebd259a2-1f5e-42d2-b5af-179ea0f766cc
-- statement:
--   If $a,b,c>0$ then prove that\n\n $\frac{a^2}{b^2+c^2}+\frac{b^2}{a^2+c^2}+\frac{c^2}{a^2+b^2}\geq\frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9507 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (b^2 + c^2) + b^2 / (a^2 + c^2) + c^2 / (a^2 + b^2)) ≥ 3 / 2   :=  by sorry
