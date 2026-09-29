-- Prove2me | solution 1 for primeZeta_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:21:37.54626+00:00
-- url     : https://prove2.me/submissions/13b1617f-a312-40d9-a00a-5b1d5f0039d8

-- Sol generated from Novelty/PrimeZetaAbscissa.lean
import Mathlib
import Definitions.Def_Novelty_PrimeZetaAbscissa
import Theorems.Thm_primeZeta_summable_iff

/-!
# The real prime zeta function and its abscissa of convergence

This file develops the elementary, fully rigorous core behind the (physically
motivated) idea of a "regularized sum of all primes".

The **prime zeta function** is the Dirichlet series
`P(s) = ∑_{p prime} p^{-s}`.  Over the reals we package it as `primeZeta`.

The central rigorous fact is that the defining series has **abscissa of
convergence exactly `1`**: it converges (absolutely) precisely when `s > 1`, and
diverges for every `s ≤ 1`.  In particular it diverges at the point `s = -1`,
where the "sum of all primes" would live.  This is the honest obstruction that
any *regularization* (analytic continuation, zeta-regularization, …) must work
around: there is simply no value of the *series itself* at `s = -1`.

The work is organized around the Mathlib lemma `Nat.Primes.summable_rpow`,
which states `Summable (fun p => (p:ℝ) ^ r) ↔ r < -1`.

## Main results

* `primeZeta_summable_iff` — the series converges iff `1 < s` (abscissa = 1).
* `primeZeta_not_summable_of_le_one` — divergence on the whole closed half-line
  `s ≤ 1`, i.e. the boundary `s = 1` and everything to its left.
* `primeZeta_not_summable_neg_one` — the concrete divergence at `s = -1`
  (the "sum of all primes" point).
* `primeZeta_pos` — strict positivity in the region of convergence.
* `primeZeta_abscissa_eq_nat_zeta` — the prime zeta series and the *full* zeta
  series `∑ n^{-s}` share the *same* abscissa of convergence `1`, even though
  (as developed in the companion bridge file) only the full zeta admits a
  Bernoulli/`-1/12` regularization.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): "The naive series ∑ p^{-s} should already pin down a
sharp threshold; the physicists' value at s = -1 cannot come from the series."
Experiment (Experimenter): Reduced every convergence claim to the single Mathlib
input `Nat.Primes.summable_rpow` with exponent `r = -s`; the threshold `r < -1`
becomes `1 < s` after `linarith`.
Analysis (Analyst): The threshold is *exactly* `1`; there is no convergence at
the boundary `s = 1` (this is morally Euler's divergence of `∑ 1/p`) and a
fortiori none at `s = -1`.  So a value at `s = -1` is "true but only after a
genuine analytic-continuation/regularization step", never from the series.
Critique (Critic): Checked that `primeZeta_summable_iff` is not vacuous and that
positivity uses an actual prime witness (`2`), not a degenerate empty sum.
Synthesis (PI): The abscissa equals that of the full zeta series, isolating the
*Euler-product* (multiplicative) content as the only place the two series differ.
-/

open scoped BigOperators








theorem solution{s : ℝ} (hs : 1 < s) : 0 < primeZeta s := by
  have hsum : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s)) :=
    (primeZeta_summable_iff s).2 hs
  have hnonneg : ∀ p : Nat.Primes, 0 ≤ (p : ℝ) ^ (-s) := by
    intro p
    have : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (p.2.pos)
    exact le_of_lt (Real.rpow_pos_of_pos this _)
  -- the prime `2` contributes a strictly positive term
  have hpos : 0 < (((⟨2, Nat.prime_two⟩ : Nat.Primes) : ℝ) ^ (-s)) := by
    have : (0 : ℝ) < ((⟨2, Nat.prime_two⟩ : Nat.Primes) : ℝ) := by norm_num
    exact Real.rpow_pos_of_pos this _
  exact hsum.tsum_pos hnonneg _ hpos
