-- Prove2me | solution 1 for lean_workbook_plus_13564
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:58:22.670574+00:00
-- url     : https://prove2.me/submissions/93226bf6-af53-4499-bf66-b058b2aa58ad

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {a b c : ℝ} (ha : a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (b - c) ^ 2 * (b + c) * (b + c - a) * (2 * a ^ 2 + b * c) + (c - a) ^ 2 * (c + a) * (c + a - b) * (2 * b ^ 2 + c * a) + (a - b) ^ 2 * (a + b) * (a + b - c) * (2 * c ^ 2 + a * b) ≥ 0 := by
  rcases ha with ⟨ha,hb,hc⟩
  have h1 : 0≤b+c-a := by linarith
  have h2 : 0≤c+a-b := by linarith
  have h3 : 0≤a+b-c := by linarith
  positivity
