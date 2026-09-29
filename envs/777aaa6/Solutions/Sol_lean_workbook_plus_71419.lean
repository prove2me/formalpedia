-- Prove2me | solution 1 for lean_workbook_plus_71419
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:17:54.938971+00:00
-- url     : https://prove2.me/submissions/cfc9d748-aeaf-4f7b-bf15-293cda9ae082

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℕ) (a b : ℝ) (hb : ∃ n, b < n) (hab : ∀ n, a ≤ b + 1/n) : a ≤ b := by
  have sourceClaim (u v : ℝ) (huv : ∀ k : ℕ, 0 < k → u ≤ v+1/(k:ℝ)) : u ≤ v := by
    by_contra hn
    have hp : 0 < u-v := by linarith
    obtain ⟨k,hk⟩ := exists_nat_one_div_lt hp
    have hb := huv (k+1) (by omega)
    norm_num only [Nat.cast_add,Nat.cast_one] at hb
    linarith
  exact sourceClaim a b (fun k _ => hab (k:ℝ))
