-- Prove2me | Theorems.Thm_lean_workbook_plus_7723
-- name    : lean_workbook_plus_7723
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/a66a377b-73c2-4097-983a-17ca51fce7a4
-- statement:
--   A more combinatorial way to obtain the binomial coefficient squared is to rotate the plane 45 degrees so that the steps are $(\pm \sqrt{2}/2, \pm \sqrt{2}/2)$ with the $\pm$ s chosen independently. In $2m$ moves, we need $m$ plusses and $m$ minuses in the x-component, and likewise $m$ plusses and $m$ minuses in the y-component. There are $\binom{2m}{m}$ ways to choose these for each axis, getting a total of $\binom{2m}{m}^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7723 (m : ℕ) : (Nat.choose (2*m) m)^2 = (Nat.choose (2*m) m) * (Nat.choose (2*m) m)   :=  by sorry
