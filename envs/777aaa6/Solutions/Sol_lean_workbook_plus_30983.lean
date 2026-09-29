-- Prove2me | solution 1 for lean_workbook_plus_30983
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:32.881982+00:00
-- url     : https://prove2.me/submissions/8ad6eb96-8c05-4a90-a9a3-41a2aeda25e9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (h₁ : a = b ∧ b = 2*c) (h₂ : a*b*c = 864) : a + b + c = 30 := by
  rcases h₁ with ⟨hab,hbc⟩
  have hf : (c-6)*(c^2+6*c+36)=0 := by rw [hab,hbc] at h₂; nlinarith [h₂]
  have hc : c=6 := by
    rcases mul_eq_zero.mp hf with h | h
    · linarith
    · nlinarith [sq_nonneg (c+3)]
  rw [hab,hbc,hc]
  norm_num
