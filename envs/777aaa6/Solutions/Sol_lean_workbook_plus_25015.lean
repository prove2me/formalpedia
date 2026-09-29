-- Prove2me | solution 1 for lean_workbook_plus_25015
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:27:58.171479+00:00
-- url     : https://prove2.me/submissions/bfc8784f-7344-4620-834a-c8c8c452a63c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a^2 / (a + b) + b^2 / (b + c) + c^2 / (c + a) ≥ (a + b + c) / 2 := by
  intro a b c ⟨ha,hb,hc⟩
  have hpair (u v : ℝ) (hu : 0 < u) (hv : 0 < v) : (3*u-v)/4 ≤ u^2/(u+v) := by
    apply (le_div_iff₀ (add_pos hu hv)).2
    nlinarith [sq_nonneg (u-v)]
  have h₁ := hpair a b ha hb
  have h₂ := hpair b c hb hc
  have h₃ := hpair c a hc ha
  linarith
