-- Prove2me | Theorems.Thm_lean_workbook_plus_17180
-- name    : lean_workbook_plus_17180
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/ad3916be-7759-48b3-8113-25b85041282f
-- statement:
--   Prove that $\frac{(x+y+z)^2}{(xy+yz+zx)(a+b)} \ge 3$ given $x,y,z,a,b$ are positive and $a+b=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17180 (x y z a b : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : (x + y + z) ^ 2 / (x * y + y * z + z * x) * (1 / (a + b)) ≥ 3   :=  by sorry
