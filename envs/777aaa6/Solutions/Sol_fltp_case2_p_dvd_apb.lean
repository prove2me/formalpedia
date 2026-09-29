-- Prove2me | solution 1 for fltp_case2_p_dvd_apb
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T11:17:08.254831+00:00
-- url     : https://prove2.me/submissions/529862ec-ec19-44ba-8db3-1b5dcd3c90c3

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (a b c : ℕ)
    (heq : a ^ p + b ^ p = c ^ p) (h_dvd_c : p ∣ c) :
    p ∣ a + b := by
  rw [← ZMod.natCast_eq_zero_iff (a + b) p]
  push_cast
  have hc : (c : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff c p).mpr h_dvd_c
  have heq_mod : (a : ZMod p) ^ p + (b : ZMod p) ^ p = (c : ZMod p) ^ p := by
    have := congr_arg (Nat.cast : ℕ → ZMod p) heq
    push_cast at this
    exact this
  rw [ZMod.pow_card, ZMod.pow_card, hc, zero_pow hp.out.pos.ne'] at heq_mod
  exact heq_mod
