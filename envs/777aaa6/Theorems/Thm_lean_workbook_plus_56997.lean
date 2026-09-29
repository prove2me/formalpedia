-- Prove2me | Theorems.Thm_lean_workbook_plus_56997
-- name    : lean_workbook_plus_56997
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/05a34737-1354-49d2-8d61-5bcca7b093e1
-- statement:
--   The actual length of the diagonal, which we will call x, is \n $ \frac {\frac {3}{2}}{400}=\frac {\frac {3}{16}}{x}$ . This simplifies out to $ x=50$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56997  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : (3 / 2) / 400 = (3 / 16) / x) :
  x = 50   :=  by sorry
