-- Prove2me | solution 1 for lean_workbook_plus_62702
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:22:14.723489+00:00
-- url     : https://prove2.me/submissions/0b436172-f621-4383-b0f4-ee30b63ab8f1

import Mathlib

namespace MinusTwoNormRepresentation

theorem norm_dvd {N a : ℕ} (ha : N ∣ a ^ 2 + 2) {x y : ℤ}
    (hxy : (x : ZMod N) + (a : ZMod N) * y = 0) :
    (N : ℤ) ∣ x ^ 2 + 2 * y ^ 2 := by
  have haZ : (a : ZMod N) ^ 2 + 2 = 0 := by
    simpa using (ZMod.natCast_eq_zero_iff (a ^ 2 + 2) N).mpr ha
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
  push_cast
  calc
    (x : ZMod N) ^ 2 + 2 * (y : ZMod N) ^ 2 =
        ((x : ZMod N) + a * y) * (x - a * y) +
          ((a : ZMod N) ^ 2 + 2) * (y : ZMod N) ^ 2 := by ring
    _ = 0 := by rw [hxy, haZ]; ring

theorem bounded_collision {N a m : ℕ} (hN : 0 < N)
    (hcard : N < (m + 1) ^ 2) :
    ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧
      -(m : ℤ) ≤ x ∧ x ≤ m ∧ -(m : ℤ) ≤ y ∧ y ≤ m ∧
      (x : ZMod N) + (a : ZMod N) * y = 0 := by
  letI : NeZero N := ⟨ne_of_gt hN⟩
  let f : Fin (m + 1) × Fin (m + 1) → ZMod N := fun u => u.1.val + a * u.2.val
  have hc : Fintype.card (ZMod N) < Fintype.card (Fin (m + 1) × Fin (m + 1)) := by
    simpa [Fintype.card_prod, ZMod.card, pow_two] using hcard
  obtain ⟨u, v, huv, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f hc
  refine ⟨(u.1.val : ℤ) - v.1.val, (u.2.val : ℤ) - v.2.val, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra h
    push_neg at h
    apply huv
    apply Prod.ext <;> apply Fin.ext <;> omega
  · have := v.1.isLt; omega
  · have := u.1.isLt; omega
  · have := v.2.isLt; omega
  · have := u.2.isLt; omega
  · change (u.1.val : ZMod N) + a * u.2.val = v.1.val + a * v.2.val at he
    push_cast
    linear_combination he

theorem small_norm {N a : ℕ} (hN : 0 < N) (ha : N ∣ a ^ 2 + 2)
    (hnonsquare : Nat.sqrt N ^ 2 < N) :
    ∃ x y : ℤ, 0 < x ^ 2 + 2 * y ^ 2 ∧
      x ^ 2 + 2 * y ^ 2 < 3 * N ∧ (N : ℤ) ∣ x ^ 2 + 2 * y ^ 2 := by
  obtain ⟨x, y, hne, hx0, hx1, hy0, hy1, hxy⟩ :=
    bounded_collision (a := a) hN (by simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' N)
  have hx : x ^ 2 ≤ (Nat.sqrt N : ℤ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (by linarith : (0 : ℤ) ≤ Nat.sqrt N + x)]
  have hy : y ^ 2 ≤ (Nat.sqrt N : ℤ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (by linarith : (0 : ℤ) ≤ Nat.sqrt N + y)]
  have hm : (Nat.sqrt N : ℤ) ^ 2 < N := by exact_mod_cast hnonsquare
  refine ⟨x, y, ?_, by nlinarith, norm_dvd ha hxy⟩
  rcases hne with hxne | hyne
  · nlinarith [sq_pos_of_ne_zero hxne, sq_nonneg y]
  · nlinarith [sq_pos_of_ne_zero hyne, sq_nonneg x]

theorem reduce_double {N x y : ℤ} (h : x ^ 2 + 2 * y ^ 2 = 2 * N) :
    ∃ u v : ℤ, N = u ^ 2 + 2 * v ^ 2 := by
  have he : Even x := by
    have hs : Even (x ^ 2) := by
      refine ⟨N - y ^ 2, ?_⟩
      nlinarith
    exact (Int.even_pow.mp hs).1
  obtain ⟨t, ht⟩ := he
  refine ⟨y, t, ?_⟩
  rw [ht] at h
  nlinarith

theorem integer_representation {N a : ℕ} (hN : 0 < N) (ha : N ∣ a ^ 2 + 2) :
    ∃ x y : ℤ, (N : ℤ) = x ^ 2 + 2 * y ^ 2 := by
  by_cases hs : Nat.sqrt N ^ 2 = N
  · refine ⟨Nat.sqrt N, 0, ?_⟩
    exact_mod_cast hs.symm
  · have hlt : Nat.sqrt N ^ 2 < N := lt_of_le_of_ne (Nat.sqrt_le' N) hs
    obtain ⟨x, y, hpos, hbound, k, hk⟩ := small_norm hN ha hlt
    have hNZ : (0 : ℤ) < N := by exact_mod_cast hN
    have hkpos : 0 < k := by nlinarith
    have hklt : k < 3 := by nlinarith
    have hkcases : k = 1 ∨ k = 2 := by omega
    rcases hkcases with rfl | rfl
    · exact ⟨x, y, by nlinarith⟩
    · exact reduce_double (N := N) (x := x) (y := y) (by nlinarith)

theorem representation {N a : ℕ} (hN : 0 < N) (ha : N ∣ a ^ 2 + 2) :
    ∃ x y : ℕ, N = x ^ 2 + 2 * y ^ 2 := by
  obtain ⟨x, y, h⟩ := integer_representation hN ha
  refine ⟨x.natAbs, y.natAbs, ?_⟩
  have hx : (x.natAbs : ℤ) ^ 2 = x ^ 2 := by simp
  have hy : (y.natAbs : ℤ) ^ 2 = y ^ 2 := by simp
  exact_mod_cast (show (N : ℤ) = (x.natAbs : ℤ) ^ 2 + 2 * (y.natAbs : ℤ) ^ 2 by
    rw [hx, hy]; exact h)

theorem source {p a : ℕ} (hp : Nat.Prime p) (ha : p ∣ a ^ 2 + 2) :
    ∃ x y : ℕ, p = x ^ 2 + 2 * y ^ 2 ∨ 2 * p = x ^ 2 + 2 * y ^ 2 := by
  obtain ⟨x, y, h⟩ := representation hp.pos ha
  exact ⟨x, y, Or.inl h⟩

end MinusTwoNormRepresentation

theorem solution (p a : ℕ) (hp : Nat.Prime p) (hpa : p ∣ a ^ 2 + 2) :
    ∃ x y : ℕ, p ∣ x ^ 2 + 2 * y ^ 2 ∨ 2 * p ∣ x ^ 2 + 2 * y ^ 2 := by
  obtain ⟨x, y, h⟩ := MinusTwoNormRepresentation.representation hp.pos hpa
  exact ⟨x, y, Or.inl (h ▸ dvd_refl _)⟩

#print axioms MinusTwoNormRepresentation.norm_dvd
#print axioms MinusTwoNormRepresentation.bounded_collision
#print axioms MinusTwoNormRepresentation.small_norm
#print axioms MinusTwoNormRepresentation.reduce_double
#print axioms MinusTwoNormRepresentation.integer_representation
#print axioms MinusTwoNormRepresentation.representation
#print axioms MinusTwoNormRepresentation.source
#print axioms solution
