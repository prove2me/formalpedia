-- Prove2me | solution 1 for lean_workbook_plus_719
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:19:24.208445+00:00
-- url     : https://prove2.me/submissions/a86c39a9-93da-423b-8a1b-748e7aa4e4ba

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℝ) : (abs (x + y) / (1 + abs (x + y))) ≤ abs x / (1 + abs x) + abs y / (1 + abs y) := by
  let a := abs x
  let b := abs y
  let c := abs (x+y)
  have ha : 0 ≤ a := abs_nonneg x
  have hb : 0 ≤ b := abs_nonneg y
  have hc : 0 ≤ c := abs_nonneg (x+y)
  have htri : c ≤ a+b := abs_add_le x y
  have hda : 0 < 1+a := by positivity
  have hdb : 0 < 1+b := by positivity
  have hdc : 0 < 1+c := by positivity
  have hdab : 0 < 1+(a+b) := by positivity
  have hm : c/(1+c) ≤ (a+b)/(1+(a+b)) := (div_le_div_iff₀ hdc hdab).2 (by nlinarith)
  have he : a/(1+a)+b/(1+b)-(a+b)/(1+(a+b)) = a*b*(2+a+b)/((1+a)*(1+b)*(1+(a+b))) := by
    field_simp [ne_of_gt hda, ne_of_gt hdb, ne_of_gt hdab]
    <;> ring
  have hp : 0 ≤ a*b*(2+a+b)/((1+a)*(1+b)*(1+(a+b))) := by positivity
  change c/(1+c) ≤ a/(1+a)+b/(1+b)
  linarith
