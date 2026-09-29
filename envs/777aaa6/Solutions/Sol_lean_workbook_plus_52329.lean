-- Prove2me | solution 1 for lean_workbook_plus_52329
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:19:04.334995+00:00
-- url     : https://prove2.me/submissions/dd534e70-14c0-4a3e-b307-3bf0d8edfb4f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ t : ℝ, t > 0 ∧ t < 1 / N → |(1 / t - 1 / 2 - 1 / (t * (t + 1))) - 1 / 2| < ε := by
  intro ε hε
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n+1, ?_⟩
  intro t ht
  have htp : 0 < t+1 := by linarith [ht.1]
  have hid : (1/t-1/2-1/(t*(t+1)))-1/2 = -t/(t+1) := by
    field_simp [ne_of_gt ht.1,ne_of_gt htp]
    ring
  rw [hid,abs_div,abs_neg,abs_of_pos ht.1,abs_of_pos htp]
  have hbound : t/(t+1) < t := by
    apply (div_lt_iff₀ htp).mpr
    nlinarith [sq_pos_of_pos ht.1]
  have htN : t < 1/((n:ℝ)+1) := by
    simpa only [Nat.cast_add,Nat.cast_one] using ht.2
  exact hbound.trans (htN.trans hn)
