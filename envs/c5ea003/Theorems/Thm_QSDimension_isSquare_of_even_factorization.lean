-- Prove2me | Theorems.Thm_QSDimension_isSquare_of_even_factorization
-- name    : QSDimension.isSquare_of_even_factorization
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:48:26.089841+00:00
-- url     : https://prove2.me/theorems/5506378f-bc58-4570-b1bf-002173f582e9
-- title:
--   A nonzero natural with all exponents even is a perfect square.
-- statement:
--   A nonzero natural with all exponents even is a perfect square.
--
--   ```lean
--   theorem QSDimension.isSquare_of_even_factorization{n : ℕ} (hn : n ≠ 0)
--       (h : ∀ p, Even (n.factorization p)) : IsSquare n := by sorry
--
--   /-! ## The quadratic-sieve specialisation -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/QSFactorBaseDimension.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/QSFactorBaseDimension.lean#L43

-- Thm stub generated from Shared/QSFactorBaseDimension.lean
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

theorem QSDimension.isSquare_of_even_factorization{n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by sorry
