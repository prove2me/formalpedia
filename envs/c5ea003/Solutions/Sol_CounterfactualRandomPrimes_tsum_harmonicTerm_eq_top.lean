-- Prove2me | solution 1 for CounterfactualRandomPrimes.tsum_harmonicTerm_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:20:57.339481+00:00
-- url     : https://prove2.me/submissions/ba2e7469-d9bb-46bd-9a88-038a916f6778

-- Sol generated from Bridges/CounterfactualRandomPrimesBorelCantelli.lean
import Mathlib
import Definitions.Def_Bridges_CounterfactualRandomPrimesBorelCantelli

/-!
# A bridge: Random primes, Borel–Cantelli, and the prime-density series

This file is a **cross-domain connector** for the *counterfactual number theory*
programme (in which the primes of arithmetic are replaced by a random or deformed
subset of `ℕ`).  The companion file `Catalog/Novelty/CounterfactualPrimesHilbert.lean`
studies a *deterministic* deformation (the Hilbert monoid `n ≡ 1 (mod 4)`) and
shows that **infinitude of primes survives** while **unique factorization
collapses**.  Here we make the *probabilistic* half of the programme precise and
connect it to analytic number theory.

## The Cramér random model

Cramér's heuristic replaces the primes by a random set `S ⊆ ℕ` in which each
integer `n` is included **independently** with probability equal to the prime
density `1 / log n` (Prime Number Theorem: `π(n) ∼ n / log n`).  We model this by
a probability space `Ω`, independent measurable events `s n = "n ∈ S"`, and a
lower bound `μ (s n) ≥ 1 / log (n+2)` on their probabilities.

## The connection proved here

The whole qualitative behaviour of the random model is governed by a single
**number-theoretic series**, the *prime-density series*
`∑ₙ 1 / log n`, whose divergence is a soft consequence of `log n ≤ n`:

* **Survival of infinitude** (`randomPrimes_infinitely_often_ae`): because the
  prime-density series **diverges** (`tsum_cramerDensity_eq_top`), the
  *second Borel–Cantelli lemma* forces `μ (limsup s) = 1`: almost surely
  infinitely many integers are "random primes".  This is the probabilistic
  shadow of *"there are infinitely many primes"*.

* **Collapse under a summable density** (`randomPrimes_finitely_often_ae`,
  `subcritical_density_collapse`): if instead the density series **converges**
  (e.g. density `1 / (n+2)²`), the *first Borel–Cantelli lemma* forces
  `μ (limsup s) = 0`: almost surely only finitely many integers are prime.

So the *phase transition* between "infinitely many primes a.s." and "finitely
many primes a.s." is located **exactly** at the convergence/divergence boundary of
the arithmetic density series — a dictionary entry translating a measure-theoretic
`0/1` law into a statement about the summability of `1 / log n`.

This is the promised bridge: **measure theory / probability (Borel–Cantelli)**
on one side, **analytic number theory (the prime-density series)** on the other.

## Genuineness of the model

The hypotheses (a probability space with independent events of prescribed
probabilities) are *satisfiable* — they hold for the product of Bernoulli
measures — so the theorems are not vacuous.  We keep the model at the level of
hypotheses to isolate the mathematical content of the bridge.
-/

open CounterfactualRandomPrimes

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal




/-- The real sequence `1/(n+2)` is **not summable** (shifted harmonic series). -/
theorem not_summable_harmonic_shift :
    ¬ Summable (fun n : ℕ => (1:ℝ) / (n + 2)) := by
  have h : ¬ Summable (fun n : ℕ => (1:ℝ) / n) := Real.not_summable_one_div_natCast
  intro hs
  apply h
  rw [← summable_nat_add_iff 2]
  simpa using hs



variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}






open CounterfactualRandomPrimes in
theorem solution:
    ∑' n : ℕ, harmonicTerm n = ⊤ := by
  by_contra h
  apply not_summable_harmonic_shift
  have hcoe : (fun n : ℕ => harmonicTerm n)
      = (fun n : ℕ => ((((1:ℝ)/(n+2)).toNNReal : ℝ≥0) : ℝ≥0∞)) := by
    funext n; rfl
  rw [hcoe] at h
  have hsummable : Summable (fun n : ℕ => (((1:ℝ)/(n+2)).toNNReal : ℝ≥0)) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp h
  have := (NNReal.summable_coe).2 hsummable
  refine this.congr ?_
  intro n
  rw [Real.coe_toNNReal]
  positivity
