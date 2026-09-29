-- Prove2me | solution 1 for lean_workbook_plus_40699
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:26.776026+00:00
-- url     : https://prove2.me/submissions/3f9747fb-29b1-4e4d-a55b-1585586f980b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (h₁ : a ≥ b ∧ b ≥ c ∧ c > 0) : (a - b + c) * (1 / a - 1 / b + 1 / c) ≥ 1 := by
  rcases h₁ with ⟨hab,hbc,hc⟩
  have hb : 0<b := lt_of_lt_of_le hc hbc
  have ha : 0<a := lt_of_lt_of_le hb hab
  have h1 : 0≤a-b := sub_nonneg.mpr hab
  have h2 : 0≤b-c := sub_nonneg.mpr hbc
  have hi : (a-b+c)*(1/a-1/b+1/c)-1=(a-b)*(b-c)*(a+c)/(a*b*c) := by field_simp; ring
  have hp : 0≤(a-b)*(b-c)*(a+c)/(a*b*c) := by positivity
  linarith
