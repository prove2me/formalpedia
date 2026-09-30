-- Prove2me | solution 1 for lean_workbook_plus_62554
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:14:23.641815+00:00
-- url     : https://prove2.me/submissions/ea104268-e4bf-4925-b347-d8f68e38e073

import Mathlib.Analysis.Complex.Basic

theorem solution (c : ℕ → ℕ)
  (d : ℕ → ℕ)
  (h₀ : ∀ n, d n = c n % 2010)
  (h₁ : ∀ n m, n ≠ m → d n ≠ d m) :
  ∃ i j, i ≠ j ∧ d i = d j := by
  have hmaps : ∀ n ∈ Finset.range 2011, d n ∈ Finset.range 2010 := by
    intro n _
    rw [Finset.mem_range, h₀]
    exact Nat.mod_lt _ (by norm_num)
  obtain ⟨i, _, j, _, hij, hd⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simp) hmaps
  exact ⟨i, j, hij, hd⟩
