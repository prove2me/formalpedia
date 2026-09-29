-- Prove2me | solution 1 for QSDimension.isSquare_of_even_factorization
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:11:26.491971+00:00
-- url     : https://prove2.me/submissions/c1ac37c1-be3a-47eb-96bd-5483e4a10f95

-- Sol generated from Shared/QSFactorBaseDimension.lean
import Mathlib
import Definitions.Def_Shared_QSFactorBaseDimension
import Definitions.Def_Shared_QSRelationPoolRandom
import Definitions.Def_Shared_SmoothCountSparsity

/-!
# The factor base the relations actually live in, and the `𝔽₂` dimension bound

The measurements of experiment 465 say that the *input statistics* of the
quadratic sieve are those of a random pool.  What is then left as the sieve's
genuine advantage is algorithmic, and this file formalises the two algebraic
facts that constitute it.

1. **The support of a relation is confined to the admissible primes.**  A
   `B`-smooth value `x^2 - N` factors only over primes `p ≤ B` for which `N` is a
   quadratic residue (`smooth_qsValue_support`).  So the exponent vectors of the
   relations do not live in `𝔽₂^{π(B)}` but in the much smaller subspace indexed
   by the admissible primes.

2. **A dimension count then produces a congruence of squares.**  Any family of
   more nonzero naturals than the size of their common support admits a nonempty
   sub-family whose product is a perfect square
   (`exists_nonempty_subset_prod_isSquare`), because their `𝔽₂` exponent vectors
   must be linearly dependent.

Combining the two gives `qs_congruence_of_squares`: `|A| + 1` smooth sieve values
suffice to build a square, where `A` is the set of *admissible* primes — half the
factor base — rather than the whole factor base.  This is the precise sense in
which the quadratic-character constraint, which costs nothing in smoothness
probability (see `Catalog.Shared.QSRelationPoolRandom`), is a *gain* in the
linear-algebra stage.

Main results:

* `isSquare_of_even_factorization` — even exponents means perfect square.
* `exists_nonempty_subset_prod_isSquare` — the `𝔽₂` dependency argument.
* `smooth_qsValue_support` — relations are supported on admissible primes.
* `qs_congruence_of_squares` — end-to-end: `|A| + 1` relations give a square.
-/

open QSDimension

open Finset



/-! ## The quadratic-sieve specialisation -/






open QSDimension in
theorem solution{n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by
  classical
  refine ⟨∏ p ∈ n.factorization.support, p ^ (n.factorization p / 2), ?_⟩
  have hself : ∏ p ∈ n.factorization.support, p ^ (n.factorization p) = n := by
    simpa [Finsupp.prod] using Nat.factorization_prod_pow_eq_self hn
  have hstep : ∏ p ∈ n.factorization.support,
      (p ^ (n.factorization p / 2) * p ^ (n.factorization p / 2))
      = ∏ p ∈ n.factorization.support, p ^ (n.factorization p) := by
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [← pow_add]
    congr 1
    obtain ⟨k, hk⟩ := h p
    omega
  rw [← Finset.prod_mul_distrib, hstep, hself]
