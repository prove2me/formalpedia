-- Prove2me | solution 1 for ChainedLabelWidth.chain_image_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T17:45:37.34019+00:00
-- url     : https://prove2.me/submissions/deb381bb-fef1-4740-9ed7-1c45069f36cb

import Mathlib
import Definitions.Def_Applications_ChainedLabelWidth
open ChainedLabelWidth Finset in
theorem solution {A B M : ℕ} (hMB : M ≤ B) (hA : 1 ≤ A) :
    (range A ×ˢ range B).image (fun p => chain M p.1 p.2)
      = range (M * (A - 1) + B) := by
  ext n
  simp only [mem_image, mem_product, mem_range, Prod.exists, chain]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    have : a * M ≤ M * (A - 1) := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left M (by omega)
    omega
  · intro hn
    rcases Nat.eq_zero_or_pos M with h0 | hpos
    · subst h0
      exact ⟨0, n, ⟨by omega, by omega⟩, by simp⟩
    · by_cases hq : n / M ≤ A - 1
      · exact ⟨n / M, n % M, ⟨by omega, lt_of_lt_of_le (Nat.mod_lt n hpos) hMB⟩,
          Nat.div_add_mod' n M⟩
      · have h1 : (A - 1) * M ≤ n := by
          have h3 := Nat.div_mul_le_self n M
          have h2 : (A - 1) * M ≤ n / M * M := Nat.mul_le_mul_right M (by omega)
          omega
        have hc : M * (A - 1) = (A - 1) * M := mul_comm _ _
        exact ⟨A - 1, n - (A - 1) * M, ⟨by omega, by omega⟩, by omega⟩
