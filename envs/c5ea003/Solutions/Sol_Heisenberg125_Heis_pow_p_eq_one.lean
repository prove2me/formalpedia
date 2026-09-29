-- Prove2me | solution 1 for Heisenberg125.Heis.pow_p_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T01:52:42.591847+00:00
-- url     : https://prove2.me/submissions/082367d2-7766-4243-984c-df7cca933abd

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} (hp : Odd p) (g : Heis p) : g ^ p = 1 := by
  -- closed form for the powers: the commutator term accumulates a binomial coefficient
  have hpow : ∀ n : ℕ, (g ^ n).a = (n : ZMod p) * g.a ∧ (g ^ n).b = (n : ZMod p) * g.b
      ∧ (g ^ n).c = (n : ZMod p) * g.c + (n.choose 2 : ZMod p) * (g.a * g.b) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨iha, ihb, ihc⟩ := ih
      have hch : ((n + 1).choose 2 : ℕ) = n.choose 2 + n := by
        simp [Nat.choose_succ_succ]
        omega
      refine ⟨?_, ?_, ?_⟩
      · rw [pow_succ, mul_a, iha]
        push_cast
        ring
      · rw [pow_succ, mul_b, ihb]
        push_cast
        ring
      · rw [pow_succ, mul_c, ihc, iha, hch]
        push_cast
        ring
  obtain ⟨ha, hb, hc⟩ := hpow p
  have h0 : (p : ZMod p) = 0 := ZMod.natCast_self p
  obtain ⟨k, hk⟩ := hp
  have hchoose : (p.choose 2 : ZMod p) = 0 := by
    have hnat : p.choose 2 = p * k := by
      rw [Nat.choose_two_right, hk]
      have h2 : 2 * k + 1 - 1 = 2 * k := by omega
      rw [h2, show (2 * k + 1) * (2 * k) = ((2 * k + 1) * k) * 2 by ring]
      exact Nat.mul_div_cancel _ (by norm_num)
    rw [hnat]
    push_cast
    rw [h0]
    ring
  ext
  · simp [ha, h0]
  · simp [hb, h0]
  · simp [hc, h0, hchoose]
