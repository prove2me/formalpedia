-- Prove2me | solution 1 for mme_CW_q6_hash_modulus_le_five_mul_Zcount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T03:19:12.503604+00:00
-- url     : https://prove2.me/submissions/bae04502-8e8e-43db-86f7-b4a9504a356d

import Mathlib

theorem solution
    {N L G : ℕ} (hsum : L + G = N) :
    4 * (Nat.choose N G) ^ 2 + 1 ≤
      5 * (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) := by
  have hLN : L ≤ N := by omega
  have hGN : G ≤ N := by omega
  have hsymm : Nat.choose N G = Nat.choose N L := by
    have h := Nat.choose_symm hGN
    have hsub : N - G = L := by omega
    simpa only [hsub] using h.symm
  have hfirst : Nat.choose N L ≤ Nat.choose (2 * N) L :=
    Nat.choose_le_choose L (by omega)
  have hsecond : Nat.choose N L ≤ Nat.choose (2 * N - L) L :=
    Nat.choose_le_choose L (by omega)
  have hXpos : 0 < Nat.choose N G := Nat.choose_pos hGN
  have hsquare :
      (Nat.choose N G) ^ 2 ≤
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L := by
    rw [hsymm, pow_two]
    exact Nat.mul_le_mul hfirst hsecond
  nlinarith
