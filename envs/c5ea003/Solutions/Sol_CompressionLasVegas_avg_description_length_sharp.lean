-- Prove2me | solution 1 for CompressionLasVegas.avg_description_length_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T22:25:33.935435+00:00
-- url     : https://prove2.me/submissions/dd523f95-5bc7-4380-a346-4ee909fc21a2

import Definitions.Def_Speculative_AutoResearch_CompressionLasVegasOWF
open scoped Classical in
open CompressionOWF CompressionLasVegas in
theorem solution (m : ℕ) :
    (∑ y ∈ bitStringsUpTo m, K (id : Str → Str) y) + 2 * 2 ^ (m + 1)
      = (m + 1) * 2 ^ (m + 1) + 2 ∧ (bitStringsUpTo m).card + 1 = 2 ^ (m + 1) := by
  have hbmem : ∀ {n : ℕ} (y : Str), y ∈ bitStrings n → y.length = n := by
    intro n y hy
    unfold bitStrings at hy
    rw [Finset.mem_image] at hy
    obtain ⟨v, _, rfl⟩ := hy
    simp
  have hbcard : ∀ n : ℕ, (bitStrings n).card = 2 ^ n := by
    intro n
    unfold bitStrings
    rw [Finset.card_image_of_injective _ List.ofFn_injective]
    simp
  have hK : ∀ y : Str, K (id : Str → Str) y = y.length := by
    intro y
    apply le_antisymm
    · exact Nat.sInf_le (s := {n | ∃ p : Str, p.length = n ∧ id p = y}) ⟨y, rfl, rfl⟩
    · apply le_csInf (s := {n | ∃ p : Str, p.length = n ∧ id p = y}) ⟨y.length, y, rfl, rfl⟩
      rintro n ⟨p, rfl, hp⟩
      simp only [id] at hp
      rw [hp]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (m + 1)) : Set ℕ) bitStrings := by
    intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro y hya hyb
    exact hab ((hbmem y hya).symm.trans (hbmem y hyb))
  have hin : ∀ ℓ, ∑ y ∈ bitStrings ℓ, K (id : Str → Str) y = ℓ * 2 ^ ℓ := by
    intro ℓ
    rw [Finset.sum_congr rfl (fun y hy => (hK y).trans (hbmem y hy)), Finset.sum_const, hbcard]
    simp [mul_comm]
  unfold bitStringsUpTo
  rw [Finset.card_biUnion hdisj, Finset.sum_biUnion hdisj]
  simp only [hin, hbcard]
  clear hdisj
  constructor
  · induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ 2 (m + 1)]
      nlinarith [ih]
  · induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ 2 (m + 1)]
      omega
