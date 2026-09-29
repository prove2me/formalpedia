-- Prove2me | solution 1 for StrangeLoop.Girth.succ_loop_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T17:46:38.131186+00:00
-- url     : https://prove2.me/submissions/9665f09b-6517-4a5d-a2bb-bc064336a9db

import Mathlib
import Definitions.Def_Novelty_StrangeLoopGirth
open StrangeLoop.Girth in
theorem solution {n k : ℕ} (v : ℕ → ZMod n) (h : IsLoopN (succR n) k v) : n ∣ k := by
  obtain ⟨hk, hstep⟩ := h
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  -- along the loop the labels increase by one each step
  have hv : ∀ i, i ≤ k' → v i = v 0 + i := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h1 : v ((i + 1) % (k' + 1)) = v i + 1 := hstep i (by omega)
      rw [Nat.mod_eq_of_lt (by omega)] at h1
      rw [h1, ih (by omega)]
      push_cast
      ring
  -- closing the loop forces `k = 0` in `ZMod n`
  have hlast : v ((k' + 1) % (k' + 1)) = v k' + 1 := hstep k' (by omega)
  rw [Nat.mod_self, hv k' le_rfl] at hlast
  have hz : ((k' + 1 : ℕ) : ZMod n) = 0 := by
    push_cast
    linear_combination -hlast
  exact (ZMod.natCast_eq_zero_iff (k' + 1) n).mp hz
