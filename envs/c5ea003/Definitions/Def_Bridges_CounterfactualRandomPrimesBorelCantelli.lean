-- Prove2me | Definitions.Def_Bridges_CounterfactualRandomPrimesBorelCantelli
-- name    : Bridges_CounterfactualRandomPrimesBorelCantelli
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:19:21.372156+00:00
-- url     : https://prove2.me/theorems/7a123d79-0407-4776-8721-bdef1cce6eff
-- title:
--   Aether Catalog definitions — Bridges_CounterfactualRandomPrimesBorelCantelli
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CounterfactualRandomPrimesBorelCantelli`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CounterfactualRandomPrimesBorelCantelli.lean by skeleton subtraction
import Mathlib

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

namespace CounterfactualRandomPrimes

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

/-- The **Cramér prime density** at `n`: the probability, in the random model,
that `n` is a "random prime".  It equals `1 / log (n+2)` (the shift by `2`
avoids `log 0` and `log 1 = 0`, keeping the density finite and positive). -/
noncomputable def cramerDensity (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / Real.log (n + 2))

/-- The (shifted) harmonic term `1 / (n+2)`, viewed in `ℝ≥0∞`. -/
noncomputable def harmonicTerm (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (n + 2))





variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}





end CounterfactualRandomPrimes


