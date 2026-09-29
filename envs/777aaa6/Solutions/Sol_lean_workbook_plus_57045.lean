-- Prove2me | solution 1 for lean_workbook_plus_57045
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:50:47.342612+00:00
-- url     : https://prove2.me/submissions/6cbdeaba-6844-4326-b4fd-48bacc1e9651

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) : x * (x - 4) ≤ 0 ↔ 0 ≤ x ∧ x ≤ 4 := by
  constructor
  · intro h
    constructor
    · by_contra hn
      have hx : x<0 := by linarith
      have hh := mul_pos_of_neg_of_neg hx (show x-4<0 by linarith)
      linarith
    · by_contra hn
      have hx : 4<x := by linarith
      have hh := mul_pos (show 0<x by linarith) (show 0<x-4 by linarith)
      linarith
  · rintro ⟨h0,h4⟩
    exact mul_nonpos_of_nonneg_of_nonpos h0 (by linarith)
