-- Prove2me | solution 1 for lean_workbook_plus_20973
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:46:29.729478+00:00
-- url     : https://prove2.me/submissions/99091ea7-9d44-4666-a2b1-f3b7fb609096

import Mathlib

set_option autoImplicit false

namespace BinaryQuadraticPrimePowerRepresentation

open Polynomial

theorem odd_prime_base {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x y : ZMod p, a * x ^ 2 + b * y ^ 2 = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hfa : (C a * X ^ 2 : Polynomial (ZMod p)).degree = 2 :=
    degree_C_mul_X_pow 2 ha
  have hfb : (C b * X ^ 2 - C 1 : Polynomial (ZMod p)).degree = 2 := by
    rw [degree_sub_C (by rw [degree_C_mul_X_pow 2 hb]; norm_num)]
    exact degree_C_mul_X_pow 2 hb
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hfa hfb
    (by simpa only [ZMod.card] using hp.eq_two_or_odd.resolve_left hp2)
  refine ⟨x, y, ?_⟩
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub] at hxy
  linear_combination hxy

theorem quadratic_lift {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    {a c x : ℤ} (hx : (2 * a * x : ZMod p) ≠ 0)
    (h : (p : ℤ) ^ n ∣ a * x ^ 2 + c) :
    ∃ z : ℤ, (2 * a * z : ZMod p) ≠ 0 ∧
      (p : ℤ) ^ (n + 1) ∣ a * z ^ 2 + c := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := h
  let t : ℤ := ((-(k : ZMod p) / (2 * a * x)).val : ℤ)
  have ht : (t : ZMod p) = -(k : ZMod p) / (2 * a * x) := by
    simp [t]
  have htprod : (2 * a * x : ZMod p) * t = -(k : ZMod p) := by
    rw [ht, mul_comm]
    exact div_mul_cancel₀ _ hx
  have he : (p : ℤ) ∣ k + 2 * a * x * t := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [htprod, add_neg_cancel]
  have hpw : (p : ℤ) ∣ (p : ℤ) ^ n := dvd_pow_self _ (by omega)
  have hi : (p : ℤ) ∣ k + 2 * a * x * t + a * (p : ℤ) ^ n * t ^ 2 := by
    exact dvd_add he (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpw a) _)
  refine ⟨x + (p : ℤ) ^ n * t, ?_, ?_⟩
  · have hz : ((p : ℤ) : ZMod p) ^ n = 0 := by
      simp [show n ≠ 0 by omega]
    push_cast at hz ⊢
    simpa only [hz, zero_mul, add_zero] using hx
  · have hz : a * (x + (p : ℤ) ^ n * t) ^ 2 + c =
        (p : ℤ) ^ n * (k + 2 * a * x * t + a * (p : ℤ) ^ n * t ^ 2) := by
      linear_combination hk
    rw [hz, pow_succ]
    exact mul_dvd_mul_left _ hi

theorem quadratic_all_powers {p : ℕ} (hp : p.Prime) {a c x : ℤ}
    (hx : (2 * a * x : ZMod p) ≠ 0) (h : (p : ℤ) ∣ a * x ^ 2 + c) :
    ∀ n : ℕ, ∃ z : ℤ, (p : ℤ) ^ n ∣ a * z ^ 2 + c := by
  have hs : ∀ k : ℕ, ∃ z : ℤ, (2 * a * z : ZMod p) ≠ 0 ∧
      (p : ℤ) ^ (k + 1) ∣ a * z ^ 2 + c := by
    intro k
    induction k with
    | zero => exact ⟨x, hx, by simpa using h⟩
    | succ k ih =>
      obtain ⟨z, hz, hd⟩ := ih
      exact quadratic_lift hp (by omega) hz hd
  intro n
  cases n with
  | zero => exact ⟨x, by simp⟩
  | succ n =>
    obtain ⟨z, _, hz⟩ := hs n
    exact ⟨z, hz⟩

theorem odd_prime_representation {p a b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : Nat.Coprime a p) (hb : Nat.Coprime b p) (n : ℕ) :
    ∃ x y : ℤ, (p : ℤ) ^ n ∣ (a : ℤ) * x ^ 2 + b * y ^ 2 - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have ha0 : (a : ZMod p) ≠ 0 := (ZMod.isUnit_iff_coprime a p).mpr ha |>.ne_zero
  have hb0 : (b : ZMod p) ≠ 0 := (ZMod.isUnit_iff_coprime b p).mpr hb |>.ne_zero
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by
    simpa only [ZMod.ringChar_zmod_n] using hp2)
  obtain ⟨u, v, huv⟩ := odd_prime_base hp hp2 ha0 hb0
  have hbase : (p : ℤ) ∣ (a : ℤ) * (u.val : ℤ) ^ 2 + b * (v.val : ℤ) ^ 2 - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    simpa only [ZMod.natCast_zmod_val, sub_eq_zero] using huv
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by intro hv; simp [hu, hv] at huv
    have hx : (2 * (b : ℤ) * (v.val : ℤ) : ZMod p) ≠ 0 := by
      simpa using mul_ne_zero (mul_ne_zero h2 hb0) hv
    have hd : (p : ℤ) ∣ (b : ℤ) * (v.val : ℤ) ^ 2 +
        ((a : ℤ) * (u.val : ℤ) ^ 2 - 1) := by
      convert hbase using 1; ring
    obtain ⟨z, hz⟩ := quadratic_all_powers hp hx hd n
    refine ⟨u.val, z, ?_⟩
    convert hz using 1; ring
  · have hx : (2 * (a : ℤ) * (u.val : ℤ) : ZMod p) ≠ 0 := by
      simpa using mul_ne_zero (mul_ne_zero h2 ha0) hu
    have hd : (p : ℤ) ∣ (a : ℤ) * (u.val : ℤ) ^ 2 +
        ((b : ℤ) * (v.val : ℤ) ^ 2 - 1) := by
      convert hbase using 1; ring
    obtain ⟨z, hz⟩ := quadratic_all_powers hp hx hd n
    refine ⟨z, v.val, ?_⟩
    convert hz using 1; ring

-- Reused ingredient: owned a5eb8775 / workbook36478, not a new claim here.
theorem dyadic_quadratic_permutation (A B C k : ℕ) (hA : Even A) (hB : Odd B) :
    Function.Bijective (fun x : ZMod (2 ^ k) => A * x ^ 2 + B * x + C) := by
  letI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by decide)⟩
  have hinj : Function.Injective (fun x : ZMod (2 ^ k) => A * x ^ 2 + B * x + C) := by
    intro x y hxy
    have hodd : Odd (A * (x.val + y.val) + B) := by
      apply Nat.odd_iff.mpr
      simp [Nat.add_mod, Nat.mul_mod, Nat.even_iff.mp hA, Nat.odd_iff.mp hB]
    have hcop := hodd.coprime_two_right.pow_right k
    have hu := (ZMod.isUnit_iff_coprime (A * (x.val + y.val) + B) (2 ^ k)).mpr hcop
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val] at hu
    apply sub_eq_zero.mp
    apply hu.mul_left_eq_zero.mp
    calc
      (x - y) * ((A : ZMod (2 ^ k)) * (x + y) + B) =
          (A * x ^ 2 + B * x + C) - (A * y ^ 2 + B * y + C) := by ring
      _ = 0 := sub_eq_zero.mpr hxy
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

theorem dyadic_seed {a b : ℕ} (ha : a % 4 = 1) (hb : b % 2 = 1) :
    ∃ y d : ℕ, a + b * y ^ 2 = 1 + 8 * d := by
  by_cases ha8 : a % 8 = 1
  · refine ⟨0, a / 8, ?_⟩
    have := Nat.mod_add_div a 8
    simpa [ha8] using this.symm
  · have ha8' : a % 8 = 5 := by omega
    have hm : (a + 4 * b) % 8 = 1 := by omega
    refine ⟨2, (a + 4 * b) / 8, ?_⟩
    have := Nat.mod_add_div (a + 4 * b) 8
    norm_num
    omega

theorem dyadic_representation {a b : ℕ} (ha : a % 4 = 1) (hb : b % 2 = 1)
    (n : ℕ) : ∃ x y : ℤ, (2 : ℤ) ^ n ∣ (a : ℤ) * x ^ 2 + b * y ^ 2 - 1 := by
  letI : NeZero (2 ^ n) := ⟨pow_ne_zero _ (by decide)⟩
  obtain ⟨y, d, hd⟩ := dyadic_seed ha hb
  have haodd : Odd a := Nat.odd_iff.mpr (by omega)
  obtain ⟨r, hr⟩ := (dyadic_quadratic_permutation (2 * a) a d n (even_two_mul a) haodd).2 0
  have hdiv : 2 ^ n ∣ 2 * a * r.val ^ 2 + a * r.val + d := by
    apply (ZMod.natCast_eq_zero_iff _ (2 ^ n)).mp
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      ZMod.natCast_zmod_val] using hr
  have hdivZ : (2 : ℤ) ^ n ∣ 2 * a * (r.val : ℤ) ^ 2 + a * (r.val : ℤ) + d := by
    exact_mod_cast hdiv
  have hdZ : (a : ℤ) + b * (y : ℤ) ^ 2 = 1 + 8 * d := by exact_mod_cast hd
  refine ⟨1 + 4 * (r.val : ℤ), y, ?_⟩
  have he : (a : ℤ) * (1 + 4 * (r.val : ℤ)) ^ 2 + b * (y : ℤ) ^ 2 - 1 =
      8 * (2 * a * (r.val : ℤ) ^ 2 + a * (r.val : ℤ) + d) := by
    linear_combination hdZ
  rw [he]
  exact dvd_mul_of_dvd_right hdivZ 8

theorem dyadic_obstruction {a b : ℕ} (ha : a % 4 = 3) (hb : b % 4 = 3)
    (x y : ℤ) : ¬ (4 : ℤ) ∣ (a : ℤ) * x ^ 2 + b * y ^ 2 - 1 := by
  intro hd
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr hd
  have ha4 : (a : ZMod 4) = 3 := by
    simpa [ha] using (ZMod.natCast_mod a 4).symm
  have hb4 : (b : ZMod 4) = 3 := by
    simpa [hb] using (ZMod.natCast_mod b 4).symm
  push_cast at h
  rw [ha4, hb4] at h
  have hbad : ∀ u v : ZMod 4, 3 * u ^ 2 + 3 * v ^ 2 - 1 ≠ 0 := by decide
  exact hbad _ _ h

theorem all_powers_iff {p a b : ℕ} (hp : p.Prime)
    (ha : Nat.Coprime a p) (hb : Nat.Coprime b p) :
    (∀ n : ℕ, ∃ x y : ℤ, (p : ℤ) ^ n ∣ (a : ℤ) * x ^ 2 + b * y ^ 2 - 1) ↔
      p ≠ 2 ∨ a % 4 = 1 ∨ b % 4 = 1 := by
  constructor
  · intro hh
    by_cases hp2 : p = 2
    · subst p
      right
      have ha2 := Nat.odd_iff.mp ha.odd_of_right
      have hb2 := Nat.odd_iff.mp hb.odd_of_right
      by_contra hn
      push_neg at hn
      have ha4 : a % 4 = 3 := by omega
      have hb4 : b % 4 = 3 := by omega
      obtain ⟨x, y, hxy⟩ := hh 2
      exact dyadic_obstruction ha4 hb4 x y (by simpa using hxy)
    · exact Or.inl hp2
  · rintro (hp2 | ha4 | hb4) n
    · exact odd_prime_representation hp hp2 ha hb n
    · by_cases hp2 : p = 2
      · subst p
        exact dyadic_representation ha4 (Nat.odd_iff.mp hb.odd_of_right) n
      · exact odd_prime_representation hp hp2 ha hb n
    · by_cases hp2 : p = 2
      · subst p
        obtain ⟨x, y, hxy⟩ := dyadic_representation hb4 (Nat.odd_iff.mp ha.odd_of_right) n
        refine ⟨y, x, ?_⟩
        convert hxy using 1; ring
      · exact odd_prime_representation hp hp2 ha hb n

theorem natural_coordinates {N a b : ℕ} {x y : ℤ}
    (h : (N : ℤ) ∣ (a : ℤ) * x ^ 2 + b * y ^ 2 - 1) :
    a * x.natAbs ^ 2 + b * y.natAbs ^ 2 ≡ 1 [MOD N] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ N).mp
  have hx : (x.natAbs : ZMod N) ^ 2 = (x : ZMod N) ^ 2 := by
    have hZ : (x.natAbs : ℤ) ^ 2 = x ^ 2 := by simp
    simpa only [Int.cast_pow, Int.cast_natCast] using congrArg (fun z : ℤ => (z : ZMod N)) hZ
  have hy : (y.natAbs : ZMod N) ^ 2 = (y : ZMod N) ^ 2 := by
    have hZ : (y.natAbs : ℤ) ^ 2 = y ^ 2 := by simp
    simpa only [Int.cast_pow, Int.cast_natCast] using congrArg (fun z : ℤ => (z : ZMod N)) hZ
  have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr h
  push_cast at hh ⊢
  rw [hx, hy]
  exact sub_eq_zero.mp hh

theorem natural_all_powers_iff {p a b : ℕ} (hp : p.Prime)
    (ha : Nat.Coprime a p) (hb : Nat.Coprime b p) :
    (∀ n : ℕ, ∃ x y : ℕ, a * x ^ 2 + b * y ^ 2 ≡ 1 [MOD p ^ n]) ↔
      p ≠ 2 ∨ a % 4 = 1 ∨ b % 4 = 1 := by
  rw [← all_powers_iff hp ha hb]
  constructor
  · intro hh n
    obtain ⟨x, y, hxy⟩ := hh n
    have hc := (ZMod.natCast_eq_natCast_iff _ _ (p ^ n)).mpr hxy
    have hd : ((p ^ n : ℕ) : ℤ) ∣ (a : ℤ) * (x : ℤ) ^ 2 + b * (y : ℤ) ^ 2 - 1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ n)).mp
      push_cast at hc ⊢
      exact sub_eq_zero.mpr hc
    exact ⟨x, y, by simpa using hd⟩
  · intro hh n
    obtain ⟨x, y, hxy⟩ := hh n
    exact ⟨x.natAbs, y.natAbs, natural_coordinates (by simpa using hxy)⟩

theorem source_odd_prime {p a b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : Nat.Coprime a p) (hb : Nat.Coprime b p) :
    ∀ n : ℕ, ∃ x y : ℕ, a * x ^ 2 + b * y ^ 2 ≡ 1 [MOD p ^ n] :=
  (natural_all_powers_iff hp ha hb).mpr (Or.inl hp2)

theorem source_counterexample : Nat.Prime 2 ∧ Nat.Coprime 3 2 ∧
    ¬ (∀ n : ℕ, ∃ x y : ℤ, (2 : ℤ) ^ n ∣ 3 * x ^ 2 + 3 * y ^ 2 - 1) := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  obtain ⟨x, y, hxy⟩ := h 2
  exact dyadic_obstruction (a := 3) (b := 3) (by decide) (by decide) x y
    (by simpa using hxy)

end BinaryQuadraticPrimePowerRepresentation

theorem solution (p a b : ℕ) (_hp : p.Prime) (_hab : a ≠ 0 ∧ b ≠ 0)
    (_hgcd1 : Nat.Coprime a p) (_hgcd2 : Nat.Coprime b p) :
    ∀ n : ℕ, ∃ x y : ℕ, p ^ n ∣ a * x ^ 2 + b * y ^ 2 - 1 := by
  intro n
  exact ⟨0, 0, by simp⟩

#print axioms BinaryQuadraticPrimePowerRepresentation.odd_prime_base
#print axioms BinaryQuadraticPrimePowerRepresentation.quadratic_lift
#print axioms BinaryQuadraticPrimePowerRepresentation.quadratic_all_powers
#print axioms BinaryQuadraticPrimePowerRepresentation.odd_prime_representation
#print axioms BinaryQuadraticPrimePowerRepresentation.dyadic_quadratic_permutation
#print axioms BinaryQuadraticPrimePowerRepresentation.dyadic_seed
#print axioms BinaryQuadraticPrimePowerRepresentation.dyadic_representation
#print axioms BinaryQuadraticPrimePowerRepresentation.dyadic_obstruction
#print axioms BinaryQuadraticPrimePowerRepresentation.all_powers_iff
#print axioms BinaryQuadraticPrimePowerRepresentation.natural_coordinates
#print axioms BinaryQuadraticPrimePowerRepresentation.natural_all_powers_iff
#print axioms BinaryQuadraticPrimePowerRepresentation.source_odd_prime
#print axioms BinaryQuadraticPrimePowerRepresentation.source_counterexample
#print axioms solution
