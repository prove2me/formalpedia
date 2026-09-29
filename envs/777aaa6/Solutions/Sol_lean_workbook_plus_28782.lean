-- Prove2me | solution 1 for lean_workbook_plus_28782
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:47:27.083567+00:00
-- url     : https://prove2.me/submissions/c5565414-5eca-432b-9a40-c92ca8638fbe

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (h : a + b > c ∧ a + c > b ∧ b + c > a) :
  (a + b - c) * (b + c - a) * (c + a - b) * a * b * c ≥ 0 := by
  rcases h with ⟨hab,hac,hbc⟩
  have ha : 0<a := by linarith
  have hb : 0<b := by linarith
  have hc : 0<c := by linarith
  have h1 : 0<a+b-c := by linarith
  have h2 : 0<b+c-a := by linarith
  have h3 : 0<c+a-b := by linarith
  positivity
