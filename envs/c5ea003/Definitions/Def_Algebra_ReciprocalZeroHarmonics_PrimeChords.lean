-- Prove2me | Definitions.Def_Algebra_ReciprocalZeroHarmonics_PrimeChords
-- name    : Algebra_ReciprocalZeroHarmonics_PrimeChords
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T09:48:41.174454+00:00
-- url     : https://prove2.me/theorems/afaecf28-be75-4fd8-a8c2-30dd2044da0d
-- title:
--   Aether Catalog definitions — Algebra_ReciprocalZeroHarmonics_PrimeChords
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.ReciprocalZeroHarmonics.PrimeChords`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/ReciprocalZeroHarmonics/PrimeChords.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_ReciprocalZeroHarmonics_Core

/-!
# Reciprocal-Zero Harmonics V: prime-indexed harmonic statistics

Direction 5 of the programme asks for an indexing rule that encodes prime structure, and asks
whether *multiplication of integers corresponds to addition of harmonic statistics*.

The reciprocal-root statistic of the degree-one Euler factor `1 - u/p` of the Riemann zeta
function is `1/p` (its unique zero is `u = p`).  Weighting each prime by its multiplicity in `n`
gives the **prime chord**

  `primeChord n = Σ_{p^k ‖ n} k/p`,

the multiplicity-sensitive harmonic statistic indexed by the primes dividing `n`.

## Main results

* `primeChord_mul` — **multiplication ↦ addition, without any coprimality hypothesis.**  For all
  nonzero `m, n`, `primeChord (m·n) = primeChord m + primeChord n`.  The answer to Direction 5 is
  therefore affirmative for the multiplicity-sensitive convention (and would be *false* for the
  set-valued convention `Σ_{p ∣ n} 1/p`, which is only additive on coprime arguments).
* `primeChord_prime_eq_harmonicSum` — the statistic is the `Core.harmonicSum` of the zero of the
  `p`-th Euler factor, so it is an instance of the same reciprocal-zero construction.
* `primeChord_prime_injective` — the statistic separates *primes*: `primeChord p = primeChord q`
  forces `p = q`.
* `primeChord_not_injective` — but it does **not** separate integers: `primeChord 4 = primeChord
  27 = 1`.  Any prime-indexed encoding built from this statistic alone necessarily identifies
  `2²` with `3³`; a faithful encoding must retain more than the harmonic value.
* `primeChord_mono_of_dvd` — divisibility monotonicity, an immediate structural consequence of
  additivity and nonnegativity.

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).** A prime-indexed harmonic statistic should convert multiplication
  into addition and should distinguish the primes.
* **Experiment (Experimenter).** Additivity is `Nat.factorization_mul` combined with
  `Finsupp.sum_add_index'`; the failure of injectivity was found by searching for coincidences
  of `k/p`, the first being `2/2 = 3/3 = 1`, i.e. `4` and `27`.
* **Analysis (Analyst).** Additivity holds *because* the statistic is a completely additive
  arithmetic function; the collision `4 ↔ 27` is unavoidable for any completely additive function
  taking rational values with small denominators.  "True but incomplete": the encoding is a
  homomorphism `(ℕ_{>0}, ·) → (ℝ, +)` and homomorphisms onto a one-dimensional target cannot be
  injective on a free monoid of infinite rank.
* **Critique (Critic).** The nonvanishing hypotheses `m, n ≠ 0` are essential
  (`Nat.factorization 0 = 0`, which would make the identity false at `0`).  The negative result
  is a genuine counterexample, not an unproved claim.
-/

namespace ReciprocalZeroHarmonics

/-- The **prime chord** of `n`: the multiplicity-weighted sum of the reciprocal zeros of the
Euler factors of `ζ` at the primes dividing `n`, `Σ_{p^k ‖ n} k/p`. -/
noncomputable def primeChord (n : ℕ) : ℝ := n.factorization.sum fun p k => (k : ℝ) / p











end ReciprocalZeroHarmonics


