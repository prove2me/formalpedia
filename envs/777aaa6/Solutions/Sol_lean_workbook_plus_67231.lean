-- Prove2me | solution 1 for lean_workbook_plus_67231
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:24:17.299018+00:00
-- url     : https://prove2.me/submissions/a93db165-32a3-4282-abdc-b5e817b57552

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace SeventhRootTraceQuadraticDescent

-- These two field identities are reused from the owned SeventhRootTraceCubic certificate.
theorem trace_identity {K : Type*} [Field K] (z : K) (hz : z ≠ 0) :
    (z - 1) * z ^ 3 * ((z + z⁻¹) ^ 3 + (z + z⁻¹) ^ 2 - 2 * (z + z⁻¹) - 1) =
      z ^ 7 - 1 := by
  field_simp
  ring

theorem trace_root {K : Type*} [Field K] (z : K) (hz : z ≠ 0)
    (hz1 : z ≠ 1) (hz7 : z ^ 7 = 1) :
    (z + z⁻¹) ^ 3 + (z + z⁻¹) ^ 2 - 2 * (z + z⁻¹) - 1 = 0 := by
  have h := trace_identity z hz
  rw [hz7, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_left
    (mul_ne_zero (sub_ne_zero.mpr hz1) (pow_ne_zero _ hz))

theorem finite_field_descent {K L : Type*} [Field K] [Fintype K]
    [Field L] [Finite L] [Algebra K L] (x : L)
    (hx : x ^ Fintype.card K = x) :
    ∃ a : K, algebraMap K L a = x := by
  apply (IsGalois.mem_range_algebraMap_iff_fixed x).mpr
  intro f
  obtain ⟨n, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K L).2 f
  have hfix : FiniteField.frobeniusAlgEquivOfAlgebraic K L x = x := hx
  have hpow : ∀ m : ℕ, (FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ m) x = x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => simp only [pow_succ, AlgEquiv.mul_apply, hfix, ih]
  exact hpow n.val

theorem trace_frobenius_fixed {K : Type*} [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (z : K) (hz : z ≠ 0) (hzp : z ^ (p + 1) = 1) :
    (z + z⁻¹) ^ p = z + z⁻¹ := by
  have hzpow : z ^ p = z⁻¹ := by
    apply mul_right_cancel₀ hz
    simpa only [inv_mul_cancel₀ hz, ← pow_succ] using hzp
  rw [add_pow_char, inv_pow, hzpow, inv_inv, add_comm]

theorem root_mod_prime (p : ℕ) (hp : p.Prime)
    (hp1 : (p : ℤ) ≡ -1 [ZMOD 7]) :
    ∃ t : ZMod p, t ^ 3 + t ^ 2 - 2 * t - 1 = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  let K := GaloisField p 2
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hd : 7 ∣ p + 1 := by
    have h : (p : ℤ) + 1 ≡ 0 [ZMOD 7] := by
      simpa using hp1.add (Int.ModEq.refl 1)
    exact_mod_cast (Int.modEq_zero_iff_dvd.mp h)
  have hcard : Nat.card K = p ^ 2 := GaloisField.card p 2 (by decide)
  have hfactor : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have := hp.one_le
    nlinarith [Nat.sub_add_cancel this,
      Nat.sub_add_cancel (show 1 ≤ p ^ 2 by nlinarith [hp.two_le])]
  have hdcard : 7 ∣ Fintype.card Kˣ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, hcard, hfactor]
    exact dvd_mul_of_dvd_right hd _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := Kˣ) 7 hdcard
  have hu7 : (u : K) ^ 7 = 1 := by
    have h := congrArg (fun v : Kˣ => (v : K)) (hu ▸ pow_orderOf_eq_one u)
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h
  have hu1 : (u : K) ≠ 1 := by
    intro h
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu
    omega
  have hup : (u : K) ^ (p + 1) = 1 := by
    obtain ⟨k, hk⟩ := hd
    rw [hk, pow_mul, hu7, one_pow]
  have ht := trace_frobenius_fixed p (u : K) (Units.ne_zero u) hup
  obtain ⟨t, htmap⟩ := finite_field_descent (K := ZMod p)
    ((u : K) + (u : K)⁻¹) (by simpa only [ZMod.card] using ht)
  refine ⟨t, (algebraMap (ZMod p) K).injective ?_⟩
  simp only [map_sub, map_add, map_pow, map_mul, map_ofNat, map_one, map_zero, htmap]
  exact trace_root _ (Units.ne_zero u) hu1 hu7

theorem arbitrarily_large_integer_polynomial_witnesses (p : ℕ) (hp : p.Prime)
    (hp1 : (p : ℤ) ≡ -1 [ZMOD 7]) (N : ℕ) :
    ∃ m : ℕ, N < m ∧ (p : ℤ) ∣ (m : ℤ) ^ 3 + (m : ℤ) ^ 2 - 2 * m - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := root_mod_prime p hp hp1
  let m := t.val + p * (N + 1)
  have hm : N < m := by
    dsimp [m]
    have := hp.two_le
    nlinarith
  refine ⟨m, hm, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
  have hc : (m : ZMod p) = t := by simp [m]
  push_cast
  rw [hc]
  exact ht

theorem natural_polynomial_cast (m : ℕ) (hm : 2 ≤ m) :
    ((m ^ 3 + m ^ 2 - 2 * m - 1 : ℕ) : ℤ) =
      (m : ℤ) ^ 3 + (m : ℤ) ^ 2 - 2 * m - 1 := by
  have hm2 : 2 * m ≤ m ^ 2 := by nlinarith
  have hsub : 2 * m ≤ m ^ 3 + m ^ 2 := by omega
  have hlast : 1 ≤ m ^ 3 + m ^ 2 - 2 * m := by
    have hpow : 1 ≤ m ^ 3 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    omega
  rw [Nat.cast_sub hlast, Nat.cast_sub hsub]
  push_cast
  rfl

theorem arbitrarily_large_natural_witnesses (p : ℕ) (hp : p.Prime)
    (hp1 : (p : ℤ) ≡ -1 [ZMOD 7]) (N : ℕ) :
    ∃ m : ℕ, N < m ∧ 2 ≤ m ∧ p ∣ m ^ 3 + m ^ 2 - 2 * m - 1 := by
  obtain ⟨m, hm, hd⟩ := arbitrarily_large_integer_polynomial_witnesses p hp hp1 (N + 1)
  have hm2 : 2 ≤ m := by omega
  refine ⟨m, by omega, hm2, ?_⟩
  exact_mod_cast (show (p : ℤ) ∣ ((m ^ 3 + m ^ 2 - 2 * m - 1 : ℕ) : ℤ) by
    rw [natural_polynomial_cast m hm2]
    exact hd)

end SeventhRootTraceQuadraticDescent

theorem solution (p : ℕ) (hp : p.Prime) (h : p ≡ -1 [ZMOD 7]) :
    ∃ n : ℕ, p ∣ n ^ 3 + n ^ 2 - 2 * n - 1 := by
  obtain ⟨n, _, _, hn⟩ :=
    SeventhRootTraceQuadraticDescent.arbitrarily_large_natural_witnesses p hp h 0
  exact ⟨n, hn⟩

#print axioms SeventhRootTraceQuadraticDescent.trace_identity
#print axioms SeventhRootTraceQuadraticDescent.trace_root
#print axioms SeventhRootTraceQuadraticDescent.finite_field_descent
#print axioms SeventhRootTraceQuadraticDescent.trace_frobenius_fixed
#print axioms SeventhRootTraceQuadraticDescent.root_mod_prime
#print axioms SeventhRootTraceQuadraticDescent.arbitrarily_large_integer_polynomial_witnesses
#print axioms SeventhRootTraceQuadraticDescent.natural_polynomial_cast
#print axioms SeventhRootTraceQuadraticDescent.arbitrarily_large_natural_witnesses
#print axioms solution
