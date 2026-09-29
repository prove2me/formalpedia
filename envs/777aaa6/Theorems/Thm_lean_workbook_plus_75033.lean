-- Prove2me | Theorems.Thm_lean_workbook_plus_75033
-- name    : lean_workbook_plus_75033
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/d69a1513-43b7-4d93-9f22-3da83ff3b819
-- statement:
--   Let $x,y\ge 0 ,4y-x\le 12,y+4x\le 20$ Prove that : \n $$9-x^2-y^2+xy+2(x+y)\le 13$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75033 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h1 : 4 * y - x ≤ 12) (h2 : y + 4 * x ≤ 20) : 9 - x ^ 2 - y ^ 2 + x * y + 2 * (x + y) ≤ 13   :=  by sorry
