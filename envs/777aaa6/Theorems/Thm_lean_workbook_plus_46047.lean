-- Prove2me | Theorems.Thm_lean_workbook_plus_46047
-- name    : lean_workbook_plus_46047
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/d7f61d27-d694-4366-911f-3f3273ff9939
-- statement:
--   Let the height of the trapezoid be $h$. Then we have $\frac{h}{\sqrt3}+4+h\sqrt3=16$, so $h=3\sqrt3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46047  (h : ℝ)
  (hh : 0 < h)
  (hh2 : (h / Real.sqrt 3 + 4 + h * Real.sqrt 3) = 16) :
  h = 3 * Real.sqrt 3   :=  by sorry
