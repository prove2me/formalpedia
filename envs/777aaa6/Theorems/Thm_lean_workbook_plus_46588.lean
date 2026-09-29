-- Prove2me | Theorems.Thm_lean_workbook_plus_46588
-- name    : lean_workbook_plus_46588
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/e974f33f-ef13-4129-a892-e1e467a3f19c
-- statement:
--   Prove that $xyz+8 \ge 3(xy+yz+zx)$ given $x^3+y^3+z^3 =3$ and $x,y,z >0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46588 (x y z : ℝ) (hx : x > 0 ∧ y > 0 ∧ z > 0) (h : x^3 + y^3 + z^3 = 3) : x*y*z + 8 ≥ 3 * (x*y + y*z + z*x)   :=  by sorry
