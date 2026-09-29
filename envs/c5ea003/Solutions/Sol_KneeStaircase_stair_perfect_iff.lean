-- Prove2me | solution 1 for KneeStaircase.stair_perfect_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:51:49.077503+00:00
-- url     : https://prove2.me/submissions/04ad59af-9e72-43a4-b972-92f0c8770730

-- Sol generated from NumberTheory/KneeStaircaseDivisorSpectrum.lean
import Mathlib
import Definitions.Def_NumberTheory_KneeStaircaseArithmetic
import Theorems.Thm_KneeStaircase_odd_two_pow_sub_one
import Theorems.Thm_KneeStaircase_one_le_two_pow
import Theorems.Thm_KneeStaircase_stair_perfect_of_mersenne_prime
import Theorems.Thm_KneeStaircase_stair_pos
/-
# The divisor spectrum of the staircase family: abundance, perfection, and the NET-47 boundary

Companion to `Catalog/NumberTheory/KneeStaircaseArithmetic.lean`, where the NET-47 knee triple
`{96, 112, 128}` at `(d = 4, ctx = 1024)` was identified with the top of the binary staircase
ladder `stair b j = 2 ^ b (2 ^ j - 1)` together with its top point `2 ^ 7`.

Here we compute the divisor sum of the whole family and classify its members.  The outcome is a
sharp arithmetic dichotomy running straight through the measured data:

* `KneeStaircase.sum_divisors_stair` — `σ(stair b j) = (2^(b+1) - 1) · σ(2^j - 1)`, from the
  2-adic splitting of the staircase normal form.
* `KneeStaircase.stair_abundant` — every staircase number with `2 ≤ j ≤ b` is **abundant**.  Both
  *jittered* knees `96 = stair 5 2` and `112 = stair 4 3` qualify.
* `KneeStaircase.stair_deficient_of_one` — the `j = 1` rungs are the powers of two, which are
  **deficient**.  The *product point* `128 = 2 ^ 7` is one of them
  (`KneeStaircase.net47_product_point_deficient`).
* `KneeStaircase.stair_perfect_of_mersenne_prime` (Euclid direction) and
  `KneeStaircase.stair_perfect_iff` (Euler direction, proved here from scratch for the family):
  for `1 ≤ b`, `stair b j` is **perfect** iff `j = b + 1` and `2 ^ j - 1` is prime.  In
  particular no rung of the weight-7 ladder is perfect (`KneeStaircase.net47_no_knee_perfect`):
  the only candidate `120 = stair 3 4` fails precisely because `15` is composite.
* `KneeStaircase.abundancy_strict_mono_shift` — the abundancy index increases strictly along the
  shift `b ↦ b + 1`, and
* `KneeStaircase.abundancy_tendsto` — a bridge to analysis: along the shift direction the
  abundancy index converges to `2 σ(2^j - 1) / (2^j - 1)`.  The staircase family therefore has a
  *finite* abundancy ceiling for each fixed number of ones; abundance in this family is a
  statement about the ratio of `b` to `j`, not about size.
* `KneeStaircase.net47_jitter_crosses_perfect_boundary` — the reading of the round: the two
  jittered knees are abundant, the product point is deficient.  The ±16 seed jitter observed at
  `(d = 4, ctx = 1024)` moves the knee across the perfect-number boundary.
-/


open KneeStaircase

open Finset

/-! ## 1.  The divisor sum of a staircase number -/

theorem sum_divisors_two_pow (b : ℕ) : ∑ d ∈ (2 ^ b).divisors, d = 2 ^ (b + 1) - 1 := by
  simp [Nat.sum_divisors_prime_pow (p := 2) Nat.prime_two, Nat.geomSum_eq]

theorem coprime_two_pow_mersenne {b j : ℕ} (hj : 1 ≤ j) : Nat.Coprime (2 ^ b) (2 ^ j - 1) :=
  Nat.Coprime.pow_left _
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (odd_two_pow_sub_one hj))

/-- **The divisor sum of the staircase family** splits along the binary normal form. -/
theorem sum_divisors_stair {b j : ℕ} (hj : 1 ≤ j) :
    ∑ d ∈ (stair b j).divisors, d
      = (2 ^ (b + 1) - 1) * ∑ d ∈ (2 ^ j - 1).divisors, d := by
  rw [stair, (coprime_two_pow_mersenne (b := b) hj).sum_divisors_mul, sum_divisors_two_pow]

theorem one_le_mersenne {j : ℕ} (hj : 1 ≤ j) : 1 ≤ 2 ^ j - 1 := by
  have h : (2:ℕ) ^ 1 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  simp only [pow_one] at h
  omega




/-! ## 2.  Abundance -/



/-! ## 3.  Perfection: Euclid and Euler for the staircase family -/




/-! ## 4.  The abundancy index along the shift direction -/



/-! ## 5.  The NET-47 reading -/







open KneeStaircase in
theorem solution{b j : ℕ} (hb : 1 ≤ b) (hj : 1 ≤ j) :
    Nat.Perfect (stair b j) ↔ j = b + 1 ∧ Nat.Prime (2 ^ j - 1) := by
  constructor
  · intro hper
    have hpos : 0 < stair b j := stair_pos hj
    have hMpos : 1 ≤ 2 ^ j - 1 := one_le_mersenne hj
    set S := ∑ d ∈ (2 ^ j - 1).divisors, d with hSdef
    set m := 2 ^ j - 1 with hmdef
    set P := (2:ℕ) ^ b with hPdef
    set A := (2:ℕ) ^ (b + 1) - 1 with hAdef
    have hP2 : 2 ≤ P := by
      have : (2:ℕ) ^ 1 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
      simpa [hPdef] using this
    have hA : A + 1 = 2 * P := by
      have h1 : (1:ℕ) ≤ 2 ^ (b + 1) := one_le_two_pow _
      have h2 : (2:ℕ) ^ (b + 1) = 2 * P := by rw [hPdef]; ring
      omega
    have hA3 : 3 ≤ A := by omega
    -- perfection, in the split form
    have hkey : A * S = (A + 1) * m := by
      have h := (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp hper
      rw [sum_divisors_stair hj, stair] at h
      rw [hA]
      calc A * S = 2 * (P * m) := h
        _ = 2 * P * m := by ring
    -- `A` is coprime to `A + 1`, hence divides `m`
    have hcop : Nat.Coprime A (A + 1) := by simp [Nat.Coprime]
    obtain ⟨t, ht⟩ : A ∣ m := hcop.dvd_of_dvd_mul_left ⟨S, hkey.symm⟩
    have htpos : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · rw [h, mul_zero] at ht; omega
      · exact h
    have hSt : S = (A + 1) * t := by
      refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < A) ?_
      rw [hkey, ht]; ring
    have hprop : ∑ d ∈ m.properDivisors, d = t := by
      have h := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := m)
      rw [← hSdef, hSt] at h
      have hexp : (A + 1) * t = A * t + t := by ring
      omega
    have htlt : t < m := by
      have h3 : 3 * t ≤ A * t := Nat.mul_le_mul_right _ hA3
      omega
    have htmem : t ∈ m.properDivisors :=
      Nat.mem_properDivisors.mpr ⟨⟨A, by rw [ht]; ring⟩, htlt⟩
    have hm2 : 2 ≤ m := by omega
    have ht1 : t = 1 := by
      by_contra hne
      have h1mem : (1:ℕ) ∈ m.properDivisors :=
        Nat.one_mem_properDivisors_iff_one_lt.mpr (by omega)
      have hsub : ({1, t} : Finset ℕ) ⊆ m.properDivisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have hpair : ∑ d ∈ ({1, t} : Finset ℕ), d = 1 + t := Finset.sum_pair (Ne.symm hne)
      have hle : ∑ d ∈ ({1, t} : Finset ℕ), d ≤ ∑ d ∈ m.properDivisors, d :=
        Finset.sum_le_sum_of_subset hsub
      omega
    have hprime : Nat.Prime m := by
      rw [← Nat.sum_properDivisors_eq_one_iff_prime, hprop, ht1]
    refine ⟨?_, hprime⟩
    have hmA : m = A := by rw [ht, ht1, mul_one]
    have hpow : (2:ℕ) ^ j = 2 ^ (b + 1) := by
      have h1 : (1:ℕ) ≤ 2 ^ j := one_le_two_pow j
      have h2 : (1:ℕ) ≤ 2 ^ (b + 1) := one_le_two_pow _
      rw [hmdef, hAdef] at hmA
      omega
    exact Nat.pow_right_injective (le_refl 2) hpow
  · rintro ⟨rfl, hp⟩
    exact stair_perfect_of_mersenne_prime hp
