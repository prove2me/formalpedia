-- Prove2me | solution 1 for lean_workbook_plus_52628
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:05:17.7912+00:00
-- url     : https://prove2.me/submissions/256590de-1cb8-4409-89c7-e7a3f01536ce

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Units
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

theorem positive_mixed_power_relation {G : Type*} [CommGroup G] [Fintype G]
    (a b : G) (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ m + n ≤ Nat.card G ∧ a ^ m * b ^ n = 1 := by
  classical
  let H := Subgroup.zpowers a
  let q := Nat.card (G ⧸ H)
  have hq : 0 < q := Nat.card_pos
  have hd : 0 < orderOf a := orderOf_pos_iff.mpr (isOfFinOrder_of_finite a)
  have hd2 : 2 ≤ orderOf a := by
    have hne : orderOf a ≠ 1 := fun he => ha (orderOf_eq_one_iff.mp he)
    omega
  have hHcard : Nat.card H = orderOf a := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_zpowers
  have hcard : q * orderOf a = Nat.card G := by
    have he := H.card_eq_card_quotient_mul_card_subgroup
    rw [hHcard] at he
    exact he.symm
  have hbq : b ^ q ∈ H := by
    apply (QuotientGroup.eq_one_iff (b ^ q)).mp
    rw [QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  have hinv : (b ^ q)⁻¹ ∈ Subgroup.zpowers a := H.inv_mem hbq
  obtain ⟨k, hk, hpow⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp hinv)
  have hklt : k < orderOf a := Finset.mem_range.mp hk
  let m := if k = 0 then orderOf a else k
  have hm : 0 < m := by
    dsimp [m]
    split_ifs with hk0 <;> omega
  have hmle : m ≤ orderOf a := by
    dsimp [m]
    split_ifs <;> omega
  have hmpow : a ^ m = (b ^ q)⁻¹ := by
    dsimp [m]
    split_ifs with hk0
    · rw [pow_orderOf_eq_one]
      simpa only [hk0, pow_zero] using hpow
    · exact hpow
  have hsize : m + q ≤ Nat.card G := by
    rw [← hcard]
    by_cases hq1 : q = 1
    · have hk0 : k ≠ 0 := by
        intro hk0
        have hi : (b ^ q)⁻¹ = 1 := by simpa only [hk0, pow_zero] using hpow.symm
        have hb1 : b = 1 := by simpa only [hq1, pow_one] using inv_eq_one.mp hi
        exact hb hb1
      simp only [m, if_neg hk0, hq1, one_mul]
      omega
    · have hq2 : 2 ≤ q := by omega
      have he : orderOf a + q ≤ q * orderOf a := by
        nlinarith [Nat.mul_le_mul_right q hd2, Nat.mul_le_mul_right (orderOf a) hq2]
      omega
  exact ⟨m, q, hm, hq, hsize, by rw [hmpow, inv_mul_cancel]⟩

theorem positive_prime_power_witness (p : ℕ) (hp : 10 < p) (hp' : Nat.Prime p) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ m + n < p ∧ (5 ^ m * 7 ^ n - 1) % p = 0 := by
  classical
  letI : Fact p.Prime := ⟨hp'⟩
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro he
    have hd := (ZMod.natCast_eq_zero_iff 5 p).mp he
    have := Nat.le_of_dvd (by norm_num : 0 < 5) hd
    omega
  have h7 : (7 : ZMod p) ≠ 0 := by
    intro he
    have hd := (ZMod.natCast_eq_zero_iff 7 p).mp he
    have := Nat.le_of_dvd (by norm_num : 0 < 7) hd
    omega
  let a : (ZMod p)ˣ := Units.mk0 (5 : ZMod p) h5
  let b : (ZMod p)ˣ := Units.mk0 (7 : ZMod p) h7
  have ha : a ≠ 1 := by
    intro he
    have hc := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) he
    change (5 : ZMod p) = 1 at hc
    have hc' : ((5 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hc
    have hm := (ZMod.natCast_eq_natCast_iff' 5 1 p).mp hc'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
    omega
  have hb : b ≠ 1 := by
    intro he
    have hc := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) he
    change (7 : ZMod p) = 1 at hc
    have hc' : ((7 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hc
    have hm := (ZMod.natCast_eq_natCast_iff' 7 1 p).mp hc'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
    omega
  obtain ⟨m, n, hm, hn, hsize, hrel⟩ := positive_mixed_power_relation a b ha hb
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ZMod.card]
  rw [hcard] at hsize
  refine ⟨m, n, hm, hn, by omega, ?_⟩
  have hrel' := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hrel
  change (5 : ZMod p) ^ m * (7 : ZMod p) ^ n = 1 at hrel'
  have hpos : 1 ≤ 5 ^ m * 7 ^ n := by
    have : 0 < 5 ^ m * 7 ^ n := by positivity
    omega
  have hz : ((5 ^ m * 7 ^ n - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub hpos, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_one]
    exact sub_eq_zero.mpr hrel'
  exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ p).mp hz)

theorem solution (p : ℕ) (hp : 10 < p) (hp' : Nat.Prime p) :
    ∃ m n : ℕ, m + n < p ∧ (5 ^ m * 7 ^ n - 1) % p = 0 := by
  obtain ⟨m, n, _, _, hs, he⟩ := positive_prime_power_witness p hp hp'
  exact ⟨m, n, hs, he⟩

#print axioms positive_mixed_power_relation
#print axioms positive_prime_power_witness
#print axioms solution
