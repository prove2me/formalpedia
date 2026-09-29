-- Prove2me | Theorems.Thm_QSDimension_exists_nonempty_subset_prod_isSquare
-- name    : QSDimension.exists_nonempty_subset_prod_isSquare
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:48:44.442268+00:00
-- url     : https://prove2.me/theorems/7026e81f-e3e8-4571-ac5d-6ad5a094d897
-- title:
--   The dimension bound behind the sieve's linear-algebra step.
-- statement:
--   **The dimension bound behind the sieve's linear-algebra step.**  If more than
--   `S.card` nonzero naturals all factor over the prime set `S`, then some nonempty
--   sub-family has a perfect-square product: their `ð½â`-exponent vectors live in a
--   space of dimension `S.card` and must be dependent.
--
--   ```lean
--   theorem QSDimension.exists_nonempty_subset_prod_isSquare{ι : Type*} [Fintype ι] [DecidableEq ι]
--       (S : Finset ℕ) (v : ι → ℕ) (hv : ∀ i, v i ≠ 0)
--       (hsupp : ∀ i, ∀ p, (v i).factorization p ≠ 0 → p ∈ S)
--       (hcard : S.card < Fintype.card ι) :
--       ∃ T : Finset ι, T.Nonempty ∧ IsSquare (∏ i ∈ T, v i) := by sorry
--   /-! ## The quadratic-sieve specialisation -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/QSFactorBaseDimension.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/QSFactorBaseDimension.lean#L60

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

theorem QSDimension.exists_nonempty_subset_prod_isSquare{ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ℕ) (v : ι → ℕ) (hv : ∀ i, v i ≠ 0)
    (hsupp : ∀ i, ∀ p, (v i).factorization p ≠ 0 → p ∈ S)
    (hcard : S.card < Fintype.card ι) :
    ∃ T : Finset ι, T.Nonempty ∧ IsSquare (∏ i ∈ T, v i) := by sorry
