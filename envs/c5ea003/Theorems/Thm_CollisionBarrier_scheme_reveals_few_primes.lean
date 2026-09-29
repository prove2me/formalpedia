-- Prove2me | Theorems.Thm_CollisionBarrier_scheme_reveals_few_primes
-- name    : CollisionBarrier.scheme_reveals_few_primes
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:26:02.442908+00:00
-- url     : https://prove2.me/theorems/8d2bbe91-ff75-4606-aa3d-24faf5bb58cf
-- title:
--   Coverage barrier.
-- statement:
--   **Coverage barrier.**  A fixed scheme with search space of size `k` and all
--   pairwise differences below `B` reveals at most `log_P B Â· kÂ²` primes `â¥ P`:
--   the primes it can expose are the large prime divisors of its `â¤ kÂ²` pairwise
--   differences, and each difference has at most `log_P B` of them.
--
--   ```lean
--   theorem CollisionBarrier.scheme_reveals_few_primes[DecidableEq α] (C : Scheme α) {P B : ℕ}
--       (hP : 1 < P) (Q : Finset ℕ)
--       (hQ : ∀ p ∈ Q, p.Prime ∧ P ≤ p ∧
--         ∃ d ∈ diffs C, 0 < d ∧ d ≤ B ∧ p ∣ d) :
--       Q.card ≤ Nat.log P B * C.space.card ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CollisionSchemeUniversalBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CollisionSchemeUniversalBarrier.lean#L120

-- Thm stub generated from Shared/CollisionSchemeUniversalBarrier.lean
import Mathlib
import Definitions.Def_Shared_CollisionSchemeUniversalBarrier

/-!
# A universal barrier for collision-based factoring schemes

The previous files analysed specific rows of the birthday-bound hierarchy
(sumset, 3SUM, `r`-SUM, structured evaluations).  Here we abstract away the way
values are produced and keep only what all of them share: a finite *search
space* together with a *value map* into `ℕ`, and the rule that a factor is
extracted as `gcd (difference of two values) N`.

Two universal theorems are proved for this abstraction.

**Span barrier** (`reveals_le_span`).  If such a scheme reveals a factor `f`
of `N`, then two of its values differ by at least `f`.  For a semiprime
`N = p * q` with `q ≤ p` and `f = p`, this forces the scheme to manipulate
numbers of size at least `√N`: no scheme whose values live in a short interval
can ever factor, whatever its arity or internal structure.

**Coverage barrier** (`scheme_reveals_few_primes`).  A *fixed* scheme reveals
very few large primes: with `k` search points and values below `B`, at most
`log_P B · k²` primes `≥ P` can divide any of its `≤ k²` pairwise differences.
Hence a scheme that must succeed on `T` different semiprimes with larger factor
`≥ P` needs `k² ≥ T / log_P B`.  The exponent games of the hierarchy change how
`k` relates to arity, but never this counting bound.

Main results:

* `reveals_le_span`, `reveals_sqrt_barrier` — the span barrier.
* `pow_card_le_of_primes_dvd` — `P ^ |Q| ≤ d` for distinct primes `≥ P`
  dividing `d`.
* `card_le_log_of_primes_dvd` — hence `|Q| ≤ log_P d`.
* `scheme_reveals_few_primes` — the coverage barrier.
* `scheme_space_lower_bound` — its contrapositive cost form.
-/

open CollisionBarrier

open Finset


variable {α : Type*}




/-! ## The span barrier -/




/-! ## The coverage barrier -/

theorem CollisionBarrier.scheme_reveals_few_primes[DecidableEq α] (C : Scheme α) {P B : ℕ}
    (hP : 1 < P) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ P ≤ p ∧
      ∃ d ∈ diffs C, 0 < d ∧ d ≤ B ∧ p ∣ d) :
    Q.card ≤ Nat.log P B * C.space.card ^ 2 := by sorry
