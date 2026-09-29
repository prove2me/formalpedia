-- Prove2me | solution 1 for Bridges.AlexanderTorus.odd_of_dvd_odd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T14:25:35.263228+00:00
-- url     : https://prove2.me/submissions/816882cb-6be4-4159-a8f1-8e62127c42e4

import Mathlib

theorem solution {N d : ℕ} (hN : Odd N) (hd : d ∣ N) : Odd d := by
  rcases Nat.even_or_odd d with he | ho
  · exfalso
    obtain ⟨k, hk⟩ := (he.two_dvd).trans hd
    rw [Nat.odd_iff] at hN
    omega
  · exact ho
