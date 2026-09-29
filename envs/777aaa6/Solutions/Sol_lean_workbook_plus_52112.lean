-- Prove2me | solution 1 for lean_workbook_plus_52112
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:23:29.494889+00:00
-- url     : https://prove2.me/submissions/ab760406-3c7b-4545-af5e-0b8b5f3af0df

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b) ≥ 1) ∧ (a = b ∧ b = c → a = b ∧ b = c) := by
  have hd1 : 0 < b+2*c := by linarith
  have hd2 : 0 < c+2*a := by linarith
  have hd3 : 0 < a+2*b := by linarith
  let R : ℝ := a/(b+2*c)+b/(c+2*a)+c/(a+2*b)
  have hq : 0 < 3*(a*b+b*c+c*a) := by positivity
  have h1 : 0 ≤ a*b*((b+2*c)-(c+2*a))^2/((b+2*c)*(c+2*a)) := by positivity
  have h2 : 0 ≤ b*c*((c+2*a)-(a+2*b))^2/((c+2*a)*(a+2*b)) := by positivity
  have h3 : 0 ≤ c*a*((a+2*b)-(b+2*c))^2/((a+2*b)*(b+2*c)) := by positivity
  have he : R*(3*(a*b+b*c+c*a))-(a+b+c)^2 =
      a*b*((b+2*c)-(c+2*a))^2/((b+2*c)*(c+2*a))+
      b*c*((c+2*a)-(a+2*b))^2/((c+2*a)*(a+2*b))+
      c*a*((a+2*b)-(b+2*c))^2/((a+2*b)*(b+2*c)) := by
    dsimp [R]
    field_simp [ne_of_gt hd1,ne_of_gt hd2,ne_of_gt hd3]
    <;> ring
  have hn : 0 ≤ R*(3*(a*b+b*c+c*a))-(a+b+c)^2 := by linarith
  have hs : 3*(a*b+b*c+c*a) ≤ (a+b+c)^2 := by
    nlinarith only [sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)]
  have sourceBound : 1 ≤ R := by
    by_contra! h
    have hp := mul_neg_of_neg_of_pos (show R-1 < 0 by linarith) hq
    nlinarith only [hn,hs,hp]
  have sourceEqualityOnly : R = 1 → a = b ∧ b = c := by
    intro h
    rw [h] at hn
    constructor <;> nlinarith [sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)]
  exact ⟨sourceBound,fun h => h⟩
