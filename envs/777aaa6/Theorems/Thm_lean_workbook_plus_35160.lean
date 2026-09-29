-- Prove2me | Theorems.Thm_lean_workbook_plus_35160
-- name    : lean_workbook_plus_35160
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/51f8c26d-7dd5-4373-b126-8aea8e2f7662
-- statement:
--   Let $x,y,z>0$ , Prove \n\n $\sum_{cyc}x^3y^3\geq \sum_{cyc}x^3y^2z$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35160 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^3 * y^3 + y^3 * z^3 + z^3 * x^3 ≥ x^3 * y^2 * z + y^3 * z^2 * x + z^3 * x^2 * y   :=  by sorry
