-- Prove2me | solution 1 for KneeStaircase.stair_abundant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:48:59.083988+00:00
-- url     : https://prove2.me/submissions/b3caebc4-47c5-4979-8fba-71b51a0df9fd

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


theorem three_le_mersenne {j : ℕ} (hj : 2 ≤ j) : 3 ≤ 2 ^ j - 1 := by
  have h : (2:ℕ) ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  norm_num at h
  omega


/-- For `n ≥ 2` the divisor sum exceeds `n` by at least one (the divisor `1`). -/
theorem succ_le_sum_divisors {n : ℕ} (hn : 2 ≤ n) : n + 1 ≤ ∑ d ∈ n.divisors, d := by
  have h1 : (1 : ℕ) ∈ n.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.mpr (by omega)
  have hsum : 1 ≤ ∑ d ∈ n.properDivisors, d :=
    Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) h1
  have := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := n)
  omega

/-! ## 2.  Abundance -/



/-! ## 3.  Perfection: Euclid and Euler for the staircase family -/




/-! ## 4.  The abundancy index along the shift direction -/



/-! ## 5.  The NET-47 reading -/







open KneeStaircase in
theorem solution{b j : ℕ} (hj : 2 ≤ j) (hbj : j ≤ b) : Nat.Abundant (stair b j) := by
  have hj1 : 1 ≤ j := by omega
  have hm3 : 3 ≤ 2 ^ j - 1 := three_le_mersenne hj
  have hS : (2 ^ j - 1) + 1 ≤ ∑ d ∈ (2 ^ j - 1).divisors, d := succ_le_sum_divisors (by omega)
  rw [Nat.abundant_iff_sum_divisors, sum_divisors_stair hj1, stair]
  set S := ∑ d ∈ (2 ^ j - 1).divisors, d with hSdef
  set M := 2 ^ j - 1 with hMdef
  set P := (2:ℕ) ^ b with hPdef
  set A := (2:ℕ) ^ (b + 1) - 1 with hAdef
  have hP1 : 1 ≤ P := one_le_two_pow b
  have hA : A + 1 = 2 * P := by
    have h1 : (1:ℕ) ≤ 2 ^ (b + 1) := one_le_two_pow _
    have h2 : (2:ℕ) ^ (b + 1) = 2 * P := by rw [hPdef]; ring
    omega
  -- the one block is dominated by the zero block
  have hMP : M + 1 ≤ P := by
    have h1 : (2:ℕ) ^ j ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hbj
    have h2 : (1:ℕ) ≤ 2 ^ j := one_le_two_pow j
    rw [hMdef, hPdef]; omega
  have hMA : M < A := by omega
  calc 2 * (P * M) = (A + 1) * M := by rw [hA]; ring
    _ = A * M + M := by ring
    _ < A * M + A := by omega
    _ = A * (M + 1) := by ring
    _ ≤ A * S := Nat.mul_le_mul_left A hS
