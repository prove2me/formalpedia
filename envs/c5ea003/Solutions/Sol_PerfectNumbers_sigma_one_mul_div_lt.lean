-- Prove2me | solution 1 for PerfectNumbers.sigma_one_mul_div_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:47:55.772135+00:00
-- url     : https://prove2.me/submissions/b77017b5-a08e-490b-b8a3-9d26ba33d979

-- Sol generated from Applications/PerfectNumbers/Abundancy.lean
import Mathlib
import Definitions.Def_Applications_PerfectNumbers_Abundancy
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The abundancy index: multiplicativity and divisibility monotonicity

The *abundancy index* of a natural number `n` is the rational number `σ₁(n) / n`,
where `σ₁(n) = ∑_{d ∣ n} d` is the sum-of-divisors function.  It measures how
"abundant" a number is: `n` is perfect exactly when its abundancy index equals `2`.

This file establishes two basic structural facts about the abundancy index:

* **Multiplicativity** (`abundancy_mul_of_coprime`): for coprime `m, n`,
  `abundancy (m * n) = abundancy m * abundancy n`.
* **Divisibility monotonicity** (`abundancy_le_of_dvd`, `abundancy_lt_of_dvd_lt`):
  if `d ∣ n` then `abundancy d ≤ abundancy n`, with strict inequality when `d < n`.

## Breaking the circular dependency

A common pitfall is to prove multiplicativity *via* a monotonicity/embedding
argument and monotonicity *via* multiplicativity, producing a circular development.
Here the two results are proved completely independently:

* Multiplicativity rests only on the multiplicativity of `σ₁` itself
  (`ArithmeticFunction.isMultiplicative_sigma`) together with the field identity
  `mul_div_mul_comm`.
* Monotonicity rests on a *direct* divisor-sum comparison, with no reference to
  multiplicativity or to any coprime factorisation: each divisor `e` of `d` is sent
  to the divisor `e * (n / d)` of `n`.  This map is injective, so the image of
  `d.divisors` is a subset of `n.divisors` whose elementwise sum is exactly
  `(n / d) · σ₁(d)`.  Comparing sums of nonnegative terms gives
  `σ₁(d) · (n / d) ≤ σ₁(n)`, i.e. `σ₁(d) · n ≤ σ₁(n) · d`, which is precisely
  `abundancy d ≤ abundancy n`.  When `d < n` the divisor `1 ∈ n.divisors` is missing
  from the image (its only preimage would require `n / d = 1`), yielding the strict
  inequality.
-/

open ArithmeticFunction Finset

open PerfectNumbers



/-!
## The core divisor-sum comparison (no multiplicativity used)

The map `e ↦ e * (n / d)` injects `d.divisors` into `n.divisors`.  Summing over the
image and comparing with the full sum over `n.divisors` gives the basic inequality
`σ₁(d) · (n / d) ≤ σ₁(n)`.
-/





/-!
## Divisibility monotonicity of the abundancy index
-/



/-!
## Multiplicativity of the abundancy index
-/



open PerfectNumbers in
theorem solution{d n : ℕ} (hdn : d ∣ n) (hlt : d < n) :
    sigma 1 d * (n / d) < sigma 1 n := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le d) hlt
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  set q := n / d with hq
  have hdq : d * q = n := Nat.mul_div_cancel' hdn
  have hqge : 2 ≤ q := by
    by_contra h
    interval_cases q <;> omega
  rw [sigma_one_apply, sigma_one_apply]
  have hinj : Set.InjOn (fun e => e * q) ↑d.divisors := by
    intro a _ b _ h
    simpa [Nat.mul_left_inj (by omega : q ≠ 0)] using h
  have himg : (∑ x ∈ d.divisors.image (fun e => e * q), x) = ∑ e ∈ d.divisors, e * q := by
    rw [Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
  have hsub : d.divisors.image (fun e => e * q) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨e, he, rfl⟩ := hx
    rw [Nat.mem_divisors] at he ⊢
    exact ⟨by rw [← hdq]; exact Nat.mul_dvd_mul_right he.1 q, by omega⟩
  have h1mem : (1 : ℕ) ∈ n.divisors := Nat.one_mem_divisors.mpr (by omega)
  have h1not : (1 : ℕ) ∉ d.divisors.image (fun e => e * q) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro e he heq
    have hepos : 0 < e := Nat.pos_of_mem_divisors he
    nlinarith
  have hcore : (∑ x ∈ d.divisors.image (fun e => e * q), x) < ∑ x ∈ n.divisors, x :=
    Finset.sum_lt_sum_of_subset hsub h1mem h1not (by norm_num) (by intro j _ _; positivity)
  calc (∑ e ∈ d.divisors, e) * q = ∑ e ∈ d.divisors, e * q := by rw [Finset.sum_mul]
    _ = ∑ x ∈ d.divisors.image (fun e => e * q), x := himg.symm
    _ < ∑ x ∈ n.divisors, x := hcore
