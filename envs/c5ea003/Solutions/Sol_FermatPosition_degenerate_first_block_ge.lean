-- Prove2me | solution 1 for FermatPosition.degenerate_first_block_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T17:57:40.843138+00:00
-- url     : https://prove2.me/submissions/574c1716-6b0e-4d37-8ba9-64b6afce8f33

import Mathlib
import Definitions.Def_NumberTheory_FermatPositionDensity
import Definitions.Def_NumberTheory_FermatPositionGeometry
import Definitions.Def_NumberTheory_FermatPositionNonlocality
open FermatPosition in
theorem solution (n : ℕ) : n + 1 ≤ posCount degHit 0 (2 ^ n) := by
  unfold posCount
  -- position `2^a - 1` gives the value `(2^a)²`, which is `3`-smooth
  have hhit : ∀ a : ℕ, degHit (0 + ((2 ^ a - 1 : ℕ) : ℤ)) := by
    intro a
    unfold degHit sieveVal
    have h1 : (1 : ℤ) + (0 + ((2 ^ a - 1 : ℕ) : ℤ)) = 2 ^ a := by
      have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      push_cast [Nat.cast_sub this]
      ring
    rw [h1, sub_zero, Nat.mem_smoothNumbers']
    intro p hp hdvd
    simp only [Int.natAbs_pow] at hdvd
    have h2 : p ∣ Int.natAbs 2 := hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow hdvd)
    have h3 := Nat.le_of_dvd (by norm_num) h2
    simp at h3
    omega
  have hinj : Function.Injective (fun a : ℕ => 2 ^ a - 1) := by
    intro a b h
    have ha : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have hb : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    have : 2 ^ a = 2 ^ b := by simp only at h; omega
    exact Nat.pow_right_injective (le_refl 2) this
  calc n + 1 = ((Finset.range (n + 1)).image (fun a : ℕ => 2 ^ a - 1)).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    _ ≤ _ := by
        apply Finset.card_le_card
        intro j hj
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
        rw [Finset.mem_range] at ha
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, hhit a⟩
        have : 2 ^ a ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
        omega
