-- Prove2me | solution 1 for FactoringLab.tendsto_recip_semiprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:45:57.283095+00:00
-- url     : https://prove2.me/submissions/3c5a19e6-6708-4fd0-8a69-72271ddf3e64

-- Sol generated from Probability/FactoringBarriers.lean
import Mathlib
import Definitions.Def_Probability_FactoringBarriers
import Theorems.Thm_FactoringLab_bigPrime_tendsto
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
theorem solution:
    Tendsto (fun n => (((3 * bigPrime n : ℕ) : ℂ))⁻¹) atTop
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) := by
  have hpos : ∀ n, 0 < (3 * bigPrime n : ℕ) := by
    intro n; have := three_lt_bigPrime n; omega
  have htop : Tendsto (fun n => ((3 * bigPrime n : ℕ) : ℝ)) atTop atTop := by
    have hm : Tendsto (fun n => (3 * bigPrime n : ℕ)) atTop atTop :=
      Filter.tendsto_atTop_mono
        (fun n => Nat.le_mul_of_pos_left (bigPrime n) (by norm_num)) bigPrime_tendsto
    exact tendsto_natCast_atTop_atTop.comp hm
  have hnorm : Tendsto (fun n => ‖(((3 * bigPrime n : ℕ) : ℂ))⁻¹‖) atTop (nhds 0) := by
    have heq : ∀ n, ‖(((3 * bigPrime n : ℕ) : ℂ))⁻¹‖ = ((3 * bigPrime n : ℕ) : ℝ)⁻¹ := by
      intro n
      rw [norm_inv, Complex.norm_natCast]
    simp only [heq]
    exact htop.inv_tendsto_atTop
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (tendsto_zero_iff_norm_tendsto_zero.2 hnorm) ?_
  filter_upwards with n
  have hne : ((3 * bigPrime n : ℕ) : ℂ) ≠ 0 := by
    have h1 : (3 * bigPrime n : ℕ) ≠ 0 := by have := hpos n; omega
    exact_mod_cast h1
  simpa using inv_ne_zero hne
