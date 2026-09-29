-- Prove2me | solution 1 for KneeStaircase.stair_perfect_of_mersenne_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:49:00.358113+00:00
-- url     : https://prove2.me/submissions/42c9891f-159e-4236-b208-673101654331

-- Sol generated from NumberTheory/KneeStaircaseDivisorSpectrum.lean
import Mathlib
import Definitions.Def_NumberTheory_KneeStaircaseArithmetic
import Theorems.Thm_KneeStaircase_odd_two_pow_sub_one
import Theorems.Thm_KneeStaircase_one_le_two_pow
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





/-! ## 2.  Abundance -/



/-! ## 3.  Perfection: Euclid and Euler for the staircase family -/

theorem sum_divisors_prime {p : ℕ} (hp : p.Prime) : ∑ d ∈ p.divisors, d = p + 1 := by
  rw [hp.divisors, Finset.sum_pair hp.one_lt.ne]
  omega



/-! ## 4.  The abundancy index along the shift direction -/



/-! ## 5.  The NET-47 reading -/







open KneeStaircase in
theorem solution{b : ℕ} (hp : Nat.Prime (2 ^ (b + 1) - 1)) :
    Nat.Perfect (stair b (b + 1)) := by
  have hj : 1 ≤ b + 1 := by omega
  have hpos : 0 < stair b (b + 1) := stair_pos hj
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, sum_divisors_stair hj, sum_divisors_prime hp,
    stair]
  set P := (2:ℕ) ^ b with hPdef
  set A := (2:ℕ) ^ (b + 1) - 1 with hAdef
  have hP1 : 1 ≤ P := one_le_two_pow b
  have hA : A + 1 = 2 * P := by
    have h1 : (1:ℕ) ≤ 2 ^ (b + 1) := one_le_two_pow _
    have h2 : (2:ℕ) ^ (b + 1) = 2 * P := by rw [hPdef]; ring
    omega
  calc A * (A + 1) = A * (2 * P) := by rw [hA]
    _ = 2 * (P * A) := by ring
