-- Prove2me | solution 1 for FactoringLab.holomorphic_rigidity_barrier
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:47:45.537241+00:00
-- url     : https://prove2.me/submissions/f328a648-8e18-4e43-9659-cdc875f4bfc9

-- Sol generated from Probability/FactoringBarriers.lean
import Mathlib
import Definitions.Def_Probability_FactoringBarriers
import Theorems.Thm_FactoringLab_bigPrime_prime
import Theorems.Thm_FactoringLab_entire_const_of_tendsto_nhdsWithin
import Theorems.Thm_FactoringLab_tendsto_recip_semiprime
import Theorems.Thm_FactoringLab_three_lt_bigPrime
/-
# Barriers I: the polynomial barrier, rational escape, holomorphic rigidity

Three of the eight barriers of the Factoring Lab framework, proved.

* `FactoringLab.polynomial_barrier` — no polynomial with rational coefficients
  computes the smaller prime factor of a semiprime.
* `FactoringLab.rational_escape_illusory` (WWW) — the same for *rational
  functions* `A/B`: passing from polynomials to quotients buys nothing.
* `FactoringLab.algebraic_barrier` — the strongest form: *no* nonzero
  polynomial relation `F(N, p) = 0` in two variables over `ℚ` holds for all
  semiprimes.  The polynomial and rational barriers are special cases.
* `FactoringLab.polynomial_barrier_counting` — a quantitative version: for a
  fixed small factor `p`, a polynomial of degree `d` can return the correct
  factor at no more than `d` semiprimes `pq`.
* `FactoringLab.holomorphic_rigidity` / `holomorphic_rigidity_barrier` (HRB) —
  an entire function that reproduces the reciprocal of the smaller prime factor
  at the reciprocals of semiprimes is forced by the identity theorem to be
  constant, which is impossible.

The proofs share one mechanism: fixing the small factor makes the sample set
accumulate (at infinity for polynomials, at `0` for the holomorphic version),
and rigidity of the function class then forces a constant, which two different
choices of the small factor contradict.
-/

open FactoringLab

open Polynomial Filter Set

/-! ### Arithmetic input: infinitely many primes above any bound -/



/-! ### The polynomial and rational barriers -/




/-! ### The algebraic barrier: no algebraic relation between `N` and `p` -/




/-! ### Holomorphic rigidity -/










open FactoringLab in
theorem solution(f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    ¬ ∀ p q : ℕ, p.Prime → q.Prime → p < q →
        f (((p * q : ℕ) : ℂ))⁻¹ = ((p : ℕ) : ℂ)⁻¹ := by
  intro h
  have hconst : ∀ z, f z = ((3 : ℕ) : ℂ)⁻¹ := by
    refine entire_const_of_tendsto_nhdsWithin hf tendsto_recip_semiprime ?_
    intro n
    exact h 3 (bigPrime n) (by norm_num) (bigPrime_prime n) (three_lt_bigPrime n)
  have h5 := h 5 7 (by norm_num) (by norm_num) (by norm_num)
  rw [hconst] at h5
  have : ((3 : ℕ) : ℂ) = ((5 : ℕ) : ℂ) := by
    have h3 : ((3 : ℕ) : ℂ) ≠ 0 := by norm_num
    have h5' : ((5 : ℕ) : ℂ) ≠ 0 := by norm_num
    field_simp at h5
    linear_combination -h5
  norm_num at this
