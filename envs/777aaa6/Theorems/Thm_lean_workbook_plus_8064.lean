-- Prove2me | Theorems.Thm_lean_workbook_plus_8064
-- name    : lean_workbook_plus_8064
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/85d1f0d1-f985-4b91-8a10-9c9e95d449d5
-- statement:
--   Let $x+y+z=s$ , $xy+yz+xz=q$ . It is $s^2 \ge 3q$ . The original is equivalent to $(s^2-3q)(s^2-q) \ge 0$ , which is obvious. Equality iff $x=y=z$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8064 (x y z s q : ℝ) (hx : x + y + z = s) (hy : x*y + y*z + z*x = q) : s^2 ≥ 3*q   :=  by sorry
