-- Prove2me | Theorems.Thm_lean_workbook_plus_75411
-- name    : lean_workbook_plus_75411
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/7b081512-caa5-43ad-b47b-546db7acbc05
-- statement:
--   Let $x,y,z$ be nonnegative positive integers. Prove $\frac{x-y}{xy+2y+1}+\frac{y-z}{zy+2z+1}+\frac{z-x}{xz+2x+1}\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75411 (x y z : ℕ) : (x - y) / (x * y + 2 * y + 1) + (y - z) / (y * z + 2 * z + 1) + (z - x) / (z * x + 2 * x + 1) ≥ 0   :=  by sorry
