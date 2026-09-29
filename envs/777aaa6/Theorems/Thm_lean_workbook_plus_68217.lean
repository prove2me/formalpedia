-- Prove2me | Theorems.Thm_lean_workbook_plus_68217
-- name    : lean_workbook_plus_68217
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/0f5d8566-74a8-4521-b737-aa23d5f563dc
-- statement:
--   prove that $xy+yz+zx\leq\frac{1}{3}$, given $x+y+z=1$ and $x,y,z \in \mathbb{R}^{+}_{0}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68217 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (hx1 : x + y + z = 1) : x * y + y * z + z * x ≤ 1 / 3   :=  by sorry
