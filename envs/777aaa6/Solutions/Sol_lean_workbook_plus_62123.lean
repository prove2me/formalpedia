-- Prove2me | solution 1 for lean_workbook_plus_62123
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:09:49.121088+00:00
-- url     : https://prove2.me/submissions/dbc0a1e5-dc58-480d-85cb-412aa6a297c2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (9 / (a + b + c)) ≤ (2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))) ∧ (2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))) ≤ (1 / a + 1 / b + 1 / c) := by
  have hp : 0<a+b := by positivity
  have hq : 0<b+c := by positivity
  have hr : 0<c+a := by positivity
  have hs : 0<a+b+c := by positivity
  have hi : 2*(1/(a+b)+1/(b+c)+1/(c+a))-9/(a+b+c)=((a-b)^2*(a+b)+(b-c)^2*(b+c)+(c-a)^2*(c+a))/((a+b)*(b+c)*(c+a)*(a+b+c)) := by field_simp; ring
  have hn : 0≤((a-b)^2*(a+b)+(b-c)^2*(b+c)+(c-a)^2*(c+a))/((a+b)*(b+c)*(c+a)*(a+b+c)) := by positivity
  have one : ∀u v:ℝ,0<u → 0<v → 4/(u+v)≤1/u+1/v := by
    intro u v hu hv
    have he : 1/u+1/v-4/(u+v)=(u-v)^2/(u*v*(u+v)) := by field_simp; ring
    have hp : 0≤(u-v)^2/(u*v*(u+v)) := by positivity
    linarith
  constructor
  · linarith
  · have h1 := one a b ha hb
    have h2 := one b c hb hc
    have h3 := one c a hc ha
    simp only [div_eq_mul_inv,one_mul] at h1 h2 h3 ⊢
    linarith only [h1,h2,h3]
