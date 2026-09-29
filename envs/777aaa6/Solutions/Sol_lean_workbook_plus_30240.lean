-- Prove2me | solution 1 for lean_workbook_plus_30240
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:17.212143+00:00
-- url     : https://prove2.me/submissions/7b9457c0-32d7-46e8-8dd9-52e730adc012

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) (h : f a ≤ f b) : ∃ c ∈ Set.Icc a b, f c = f a + (f b - f a) / (b - a) * (c - a) := by
  intros
  grind
