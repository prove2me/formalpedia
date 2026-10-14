-- Prove2me | solution 1 for Beal_Conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T03:51:47.393954+00:00
-- url     : https://prove2.me/submissions/46369fbd-5563-40d5-8c82-3ec15cb12ae0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Beal_primitive_exponent_normalization
import Theorems.Thm_Beal_primitive_reduced_exponents
import Mathlib.NumberTheory.FLT.Four

theorem solution : ∀ {A B C x y z : ℕ},
    A ≠ 0 → B ≠ 0 → C ≠ 0 → 2 < x → 2 < y → 2 < z →
    A ^ x + B ^ y = C ^ z → 1 < Finset.gcd ({A, B, C} : Finset ℕ) id := by
  intro A B C x y z hA hB hC hx hy hz he
  by_contra hnot
  have hg0 : Finset.gcd ({A, B, C} : Finset ℕ) id ≠ 0 := by
    apply Finset.gcd_ne_zero_iff.mpr
    exact ⟨A, by simp, hA⟩
  have hg : Finset.gcd ({A, B, C} : Finset ℕ) id = 1 := by omega
  obtain ⟨a, b, c, p, q, r, ha, hb, hc, hp, hq, hr,
    _, _, _, hap, hbq, hcr, hab, hac, hbc⟩ :=
    Beal.primitive_exponent_normalization A B C x y z hA hB hC hx hy hz hg he
  have he' : a ^ p + b ^ q = c ^ r := by rw [hap, hbq, hcr, he]
  have hprime : Nat.Prime p ∨ Nat.Prime q ∨ Nat.Prime r := by
    rcases hp with rfl | hp
    · rcases hq with rfl | hq
      · rcases hr with rfl | hr
        · exact False.elim (fermatLastTheoremFour a b c ha hb hc he')
        · exact Or.inr (Or.inr hr.1)
      · exact Or.inr (Or.inl hq.1)
    · exact Or.inl hp.1
  by_cases hpq : p ≤ q
  · exact Beal.primitive_reduced_exponents ha hb hc hp hq hr hpq hprime hab hac hbc he'
  · have hqp : q ≤ p := by omega
    have hprime' : Nat.Prime q ∨ Nat.Prime p ∨ Nat.Prime r := by
      rcases hprime with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    apply Beal.primitive_reduced_exponents hb ha hc hq hp hr hqp hprime' hab.symm hbc hac
    simpa [Nat.add_comm] using he'
