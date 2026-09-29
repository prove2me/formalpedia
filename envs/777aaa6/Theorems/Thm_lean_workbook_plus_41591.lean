-- Prove2me | Theorems.Thm_lean_workbook_plus_41591
-- name    : lean_workbook_plus_41591
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/849ba08a-f61f-49ae-a9c4-23338a568c9e
-- statement:
--   If the boats have been moving for time $ t$ hours, then Boat A has moved $ 12t$ km while Boat B has moved $ 18t$ ; by Pythagoras, the distance between them is $ \sqrt{(12t)^2+(18t)^2}=6\sqrt{13}t$ . Hence the rate of change of the distance between the boats is $ \frac{6\sqrt{13}t}{t}=6\sqrt{13}\ \textrm{km}\,\textrm{h}^{-1}$ . This rate is constant, however long the boats have been travelling.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41591  (t : ℝ)
  (h₀ : 0 < t) :
  Real.sqrt ((12 * t)^2 + (18 * t)^2) = 6 * Real.sqrt 13 * t   :=  by sorry
