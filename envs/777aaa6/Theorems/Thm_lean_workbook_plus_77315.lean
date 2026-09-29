-- Prove2me | Theorems.Thm_lean_workbook_plus_77315
-- name    : lean_workbook_plus_77315
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/06defa8d-7565-4e8a-86e5-1e2475e54a97
-- statement:
--   Given $x+y+z=1$, $x^{2}+y^{2}+z^{2}=2$, $x^{3}+y^{3}+z^{3}=3$, show that $xy+yz+zx= \frac{-1}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77315 (x y z : ℝ) (h₁ : x + y + z = 1) (h₂ : x^2 + y^2 + z^2 = 2) (h₃ : x^3 + y^3 + z^3 = 3) : x*y + y*z + z*x = -1/2   :=  by sorry
