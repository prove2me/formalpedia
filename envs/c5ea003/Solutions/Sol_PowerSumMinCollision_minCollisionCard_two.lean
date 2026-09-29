-- Prove2me | solution 1 for PowerSumMinCollision.minCollisionCard_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T11:11:43.643669+00:00
-- url     : https://prove2.me/submissions/2231f02c-5835-4c7a-b91b-e93d30d48960

import Mathlib
import Definitions.Def_Probability_PowerSumMinimalCollision
open PowerSumMinCollision Multiset in
theorem solution {N : ℕ} (hN : 4 ≤ N) : minCollisionCard N 2 = 3 := by
  -- witness of size 3: `{0,3,3}` and `{1,1,4}` agree in orders 0, 1 and 2
  have hwit : IsCollision N 2 ({0, 3, 3} : Multiset ℕ) ({1, 1, 4} : Multiset ℕ) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> omega
    · intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> omega
    · intro k hk
      interval_cases k <;> decide
    · decide
  have h3mem : 3 ∈ collisionSizes N 2 := ⟨_, _, hwit, by decide⟩
  -- no collision of size 0, 1 or 2
  have hex : ∀ n ∈ collisionSizes N 2, 3 ≤ n := by
    rintro n ⟨s, t, ⟨hs, ht, hpow, hne⟩, rfl⟩
    have h0 : Multiset.card s = Multiset.card t := by
      have h := hpow 0 (by omega)
      simpa using h
    by_contra hlt
    push_neg at hlt
    have hc : Multiset.card s = 0 ∨ Multiset.card s = 1 ∨ Multiset.card s = 2 := by omega
    rcases hc with h | h | h
    · have hs0 : s = 0 := Multiset.card_eq_zero.mp h
      have ht0 : t = 0 := Multiset.card_eq_zero.mp (by rw [← h0, h])
      exact hne (by rw [hs0, ht0])
    · obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h
      obtain ⟨b, hb⟩ := Multiset.card_eq_one.mp (show Multiset.card t = 1 by rw [← h0, h])
      have h1 := hpow 1 (by omega)
      rw [ha, hb] at h1
      simp at h1
      exact hne (by rw [ha, hb, h1])
    · -- the interesting case: equal sums and equal sums of squares pin the pair down
      obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp h
      obtain ⟨c, d, hcd⟩ := Multiset.card_eq_two.mp (show Multiset.card t = 2 by rw [← h0, h])
      have h1 := hpow 1 (by omega)
      have h2 := hpow 2 (by omega)
      rw [hab, hcd] at h1 h2
      simp [pow_one] at h1
      simp at h2
      have H1 : (a : ℤ) + b = (c : ℤ) + d := by exact_mod_cast h1
      have H2 : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by exact_mod_cast h2
      -- equal sum and equal sum of squares force equal product
      have hprod : (c : ℤ) * d = (a : ℤ) * b := by nlinarith [H1, H2]
      -- so `a` is a root of the quadratic with roots `c`, `d`
      have hfac : ((a : ℤ) - c) * ((a : ℤ) - d) = 0 := by
        linear_combination (a : ℤ) * H1 + hprod
      refine hne ?_
      rcases mul_eq_zero.mp hfac with hz | hz
      · have hac : a = c := by exact_mod_cast sub_eq_zero.mp hz
        have hbd : b = d := by
          have : (b : ℤ) = d := by rw [hac] at H1; linarith
          exact_mod_cast this
        rw [hab, hcd, hac, hbd]
      · have had : a = d := by exact_mod_cast sub_eq_zero.mp hz
        have hbc : b = c := by
          have : (b : ℤ) = c := by rw [had] at H1; linarith
          exact_mod_cast this
        rw [hab, hcd, had, hbc]
        exact Multiset.pair_comm d c
  show sInf (collisionSizes N 2) = 3
  have hnon : (collisionSizes N 2).Nonempty := ⟨3, h3mem⟩
  have hle : sInf (collisionSizes N 2) ≤ 3 := Nat.sInf_le h3mem
  have hge : 3 ≤ sInf (collisionSizes N 2) := hex _ (Nat.sInf_mem hnon)
  omega
