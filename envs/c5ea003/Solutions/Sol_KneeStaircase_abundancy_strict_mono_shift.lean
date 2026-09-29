-- Prove2me | solution 1 for KneeStaircase.abundancy_strict_mono_shift
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:46:23.623168+00:00
-- url     : https://prove2.me/submissions/f1b0429a-ac89-408d-a1fe-609ee2d744bf

-- Sol generated from NumberTheory/KneeStaircaseDivisorSpectrum.lean
import Mathlib
import Definitions.Def_NumberTheory_KneeStaircaseArithmetic
import Theorems.Thm_KneeStaircase_odd_two_pow_sub_one
import Theorems.Thm_KneeStaircase_one_le_two_pow
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


/-- The divisor sum of a positive number is positive (the divisor `1`). -/
theorem one_le_sum_divisors {n : ℕ} (hn : n ≠ 0) : 1 ≤ ∑ d ∈ n.divisors, d :=
  Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) (Nat.one_mem_divisors.mpr hn)


/-! ## 2.  Abundance -/



/-! ## 3.  Perfection: Euclid and Euler for the staircase family -/




/-! ## 4.  The abundancy index along the shift direction -/



/-! ## 5.  The NET-47 reading -/







open KneeStaircase in
theorem solution{b j : ℕ} (hj : 1 ≤ j) :
    (∑ d ∈ (stair b j).divisors, d) * stair (b + 1) j
      < (∑ d ∈ (stair (b + 1) j).divisors, d) * stair b j := by
  have hMpos : 1 ≤ 2 ^ j - 1 := one_le_mersenne hj
  have hSpos : 1 ≤ ∑ d ∈ (2 ^ j - 1).divisors, d := one_le_sum_divisors (by omega)
  rw [sum_divisors_stair (b := b) hj, sum_divisors_stair (b := b + 1) hj, stair, stair]
  set S := ∑ d ∈ (2 ^ j - 1).divisors, d with hSdef
  set m := 2 ^ j - 1 with hmdef
  set P := (2:ℕ) ^ b with hPdef
  set A := (2:ℕ) ^ (b + 1) - 1 with hAdef
  set A' := (2:ℕ) ^ (b + 1 + 1) - 1 with hA'def
  have hP1 : 1 ≤ P := one_le_two_pow b
  have hA : A + 1 = 2 * P := by
    have h1 : (1:ℕ) ≤ 2 ^ (b + 1) := one_le_two_pow _
    have h2 : (2:ℕ) ^ (b + 1) = 2 * P := by rw [hPdef]; ring
    omega
  have hA' : A' + 1 = 4 * P := by
    have h1 : (1:ℕ) ≤ 2 ^ (b + 1 + 1) := one_le_two_pow _
    have h2 : (2:ℕ) ^ (b + 1 + 1) = 4 * P := by rw [hPdef]; ring
    omega
  have hAA : A' = 2 * A + 1 := by omega
  have hPA : (2:ℕ) ^ (b + 1) = A + 1 := by
    have h2 : (2:ℕ) ^ (b + 1) = 2 * P := by rw [hPdef]; ring
    omega
  rw [hPA, hAA]
  have hSm : 1 ≤ S * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc A * S * ((A + 1) * m) = (2 * A * P) * (S * m) := by rw [hA]; ring
    _ < (2 * A * P + P) * (S * m) := by
        have : 0 < P * (S * m) := Nat.mul_pos (by omega) (by omega)
        nlinarith
    _ = (2 * A + 1) * S * (P * m) := by ring
