-- Prove2me | solution 1 for WorkbookSyntax.plus_45249
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:11:52.318719+00:00
-- url     : https://prove2.me/submissions/6542c40d-fbe7-4f65-938a-4695fb3c28a4

import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution : ∀ n : ℕ, 1 < n → ∑ k ∈ Finset.filter (fun k => Nat.gcd k n = 1) (Finset.Icc 1 n), 1 = Nat.totient n   := by
  intro n hn
  rw [Nat.totient_eq_card_coprime, Finset.card_eq_sum_ones]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, Nat.coprime_iff_gcd_eq_one]
  constructor
  · rintro ⟨⟨hk, hkn⟩, hcop⟩
    have hne : k ≠ n := by
      intro heq
      subst k
      simp at hcop
      omega
    exact ⟨lt_of_le_of_ne hkn hne, by simpa [Nat.gcd_comm] using hcop⟩
  · rintro ⟨hkn, hcop⟩
    have hk : k ≠ 0 := by
      intro heq
      subst k
      simp at hcop
      omega
    exact ⟨⟨by omega, hkn.le⟩, by simpa [Nat.gcd_comm] using hcop⟩
#print axioms solution
