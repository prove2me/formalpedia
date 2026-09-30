-- Prove2me | solution 1 for lean_workbook_plus_67057
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:20:55.678572+00:00
-- url     : https://prove2.me/submissions/4d72214c-4472-4a64-91bb-24a24bb6ab84

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

theorem solution (S : Finset ℕ)
    (h₀ : ∀ n : ℕ, n ∈ S ↔ 10000 ≤ n ∧ n ≤ 99999 ∧ n % 11 = 0) :
    S.card = 8181 := by
  have hS : S = (Finset.Icc 910 9090).image (fun k : ℕ => 11 * k) := by
    ext n
    rw [h₀, Finset.mem_image]
    constructor
    · rintro ⟨hlo, hhi, hmod⟩
      refine ⟨n / 11, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩ <;> omega
    · rintro ⟨k, hk, rfl⟩
      have hk' := Finset.mem_Icc.mp hk
      omega
  have hinj : Function.Injective (fun k : ℕ => 11 * k) := by
    intro a b h
    change 11 * a = 11 * b at h
    omega
  rw [hS, Finset.card_image_of_injective _ hinj]
  norm_num
