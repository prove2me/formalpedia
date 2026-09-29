-- Prove2me | solution 1 for stabilization_from_bounded_monotone_nat
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T06:45:35.742545+00:00
-- url     : https://prove2.me/submissions/4f4b1219-4600-4708-9425-d81c535cf77a

import Mathlib
import Definitions.Def_Bridges_NeuralCoding_AlgebraEMLClosureComputation
theorem solution (c : ℕ → ℕ) (B : ℕ)
    (hMono : Monotone c)
    (hBound : ∀ n, c n ≤ B)
    (hOnceStable : ∀ n, c n = c (n + 1) → ∀ m, n ≤ m → c m = c n) :
    ∃ N ≤ B, StabilizesAt c N := by
  -- a bounded monotone sequence must pause within the first `B` steps
  have hpause : ∃ n ≤ B, c n = c (n + 1) := by
    by_contra h
    push_neg at h
    have hgrow : ∀ n ≤ B + 1, n ≤ c n := by
      intro n
      induction n with
      | zero => intro _; exact Nat.zero_le _
      | succ n ih =>
        intro hn
        have h1 := ih (by omega)
        have h2 : c n < c (n + 1) := lt_of_le_of_ne (hMono (Nat.le_succ n)) (h n (by omega))
        omega
    have h1 := hgrow (B + 1) le_rfl
    have h2 := hBound (B + 1)
    omega
  -- and once it pauses it is stable forever
  obtain ⟨n, hnB, hn⟩ := hpause
  exact ⟨n, hnB, fun m hm => hOnceStable n hn m hm⟩
