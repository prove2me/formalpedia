-- Prove2me | Theorems.Thm_lean_workbook_plus_62680
-- name    : lean_workbook_plus_62680
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/21627529-9495-48bc-aed2-5753bcc4ac33
-- statement:
--   Let $x=ab$ \n \n $a+b=2$ result $a^2+b^2=4-2x$ \n \n We gest prove $x(3-2x)\leq{\frac{9}{8}}$ \n \n Or $(4x-3)^2\geq0$ . \n \n Equality holds for $a=\frac{1}{2}$ $b=\frac{3}{2}$ or viceversa.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62680  (x : ℝ)
  (a b : ℝ)
  (h₀ : x = a * b)
  (h₁ : a + b = 2) :
  x * (3 - 2 * x) ≤ 9 / 8   :=  by sorry
