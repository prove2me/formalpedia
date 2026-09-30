-- Prove2me | solution 1 for WeakGoldbach.singular_series_factor_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-12T01:18:23.567856+00:00
-- url     : https://prove2.me/submissions/1e1c264d-c241-4585-8d90-9d89720385c2

import Mathlib

theorem solution (n : ℕ) :
    1 ≤ ∏ p ∈ n.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  calc (1 : ℝ) = ∏ _p ∈ n.primeFactors.filter (2 < ·), (1 : ℝ) :=
        (Finset.prod_const_one).symm
    _ ≤ ∏ p ∈ n.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
        apply Finset.prod_le_prod
        · intro i _; exact zero_le_one
        · intro p hp
          rw [Finset.mem_filter] at hp
          obtain ⟨hpf, hp2⟩ := hp
          have hpP : Nat.Prime p := (Nat.mem_primeFactors.mp hpf).1
          have h2 : (2 : ℝ) < p := by exact_mod_cast hp2
          rw [one_le_div (by linarith)]
          linarith
