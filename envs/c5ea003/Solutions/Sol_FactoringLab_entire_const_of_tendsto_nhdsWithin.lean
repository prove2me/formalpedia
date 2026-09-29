-- Prove2me | solution 1 for FactoringLab.entire_const_of_tendsto_nhdsWithin
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:34:51.556578+00:00
-- url     : https://prove2.me/submissions/8db093ea-02df-47ad-b0d2-b7773ed9695c

-- Sol generated from Probability/FactoringBarriers.lean
import Mathlib
import Definitions.Def_Probability_FactoringBarriers
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
theorem solution{f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {u : ℕ → ℂ} (hu : Tendsto u atTop (nhdsWithin 0 {(0 : ℂ)}ᶜ)) {c : ℂ}
    (hval : ∀ n, f (u n) = c) : ∀ z, f z = c := by
  have hg : AnalyticOnNhd ℂ (fun z => f z - c) Set.univ := by
    intro z _
    exact (hf.analyticAt z).sub analyticAt_const
  have hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, f z - c = 0 :=
    hu.frequently (Filter.Eventually.frequently
      (Filter.Eventually.of_forall (fun n => by rw [hval n]; ring)))
  have := hg.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (isPreconnected_univ) (Set.mem_univ 0) hfreq
  intro z
  have hz := this (Set.mem_univ z)
  simpa [sub_eq_zero] using hz
