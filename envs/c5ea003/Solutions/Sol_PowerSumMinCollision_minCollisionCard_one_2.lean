-- Prove2me | solution 2 for PowerSumMinCollision.minCollisionCard_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:48:08.649823+00:00
-- url     : https://prove2.me/submissions/72281a19-d83b-48bf-845e-a30eeca873e7

import Mathlib
import Definitions.Def_Probability_PowerSumMinimalCollision
open PowerSumMinCollision Multiset in
theorem solution {N : ℕ} (hN : 2 ≤ N) : minCollisionCard N 1 = 2 := by
  -- witness of size 2: `{0, 2}` and `{1, 1}` share cardinality and sum
  have hwit : IsCollision N 1 ({0, 2} : Multiset ℕ) ({1, 1} : Multiset ℕ) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> omega
    · intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> omega
    · intro k hk
      interval_cases k <;> decide
    · decide
  have h2mem : 2 ∈ collisionSizes N 1 := ⟨_, _, hwit, by decide⟩
  -- and none of size 0 or 1
  have hex : ∀ n ∈ collisionSizes N 1, 2 ≤ n := by
    rintro n ⟨s, t, ⟨hs, ht, hpow, hne⟩, rfl⟩
    have h0 : Multiset.card s = Multiset.card t := by
      have h := hpow 0 (by omega)
      simpa using h
    by_contra hlt
    push_neg at hlt
    have hc : Multiset.card s = 0 ∨ Multiset.card s = 1 := by omega
    rcases hc with h | h
    · have hs0 : s = 0 := Multiset.card_eq_zero.mp h
      have ht0 : t = 0 := Multiset.card_eq_zero.mp (by rw [← h0, h])
      exact hne (by rw [hs0, ht0])
    · obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h
      obtain ⟨b, hb⟩ := Multiset.card_eq_one.mp (show Multiset.card t = 1 by rw [← h0, h])
      have h1 := hpow 1 (by omega)
      rw [ha, hb] at h1
      simp at h1
      exact hne (by rw [ha, hb, h1])
  show sInf (collisionSizes N 1) = 2
  have hnon : (collisionSizes N 1).Nonempty := ⟨2, h2mem⟩
  have hle : sInf (collisionSizes N 1) ≤ 2 := Nat.sInf_le h2mem
  have hge : 2 ≤ sInf (collisionSizes N 1) := hex _ (Nat.sInf_mem hnon)
  omega
