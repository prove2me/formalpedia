-- Prove2me | Definitions.Def_Shared_CollisionSchemeUniversalBarrier
-- name    : Shared_CollisionSchemeUniversalBarrier
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:49:26.919891+00:00
-- url     : https://prove2.me/theorems/c5021197-feba-485c-bedd-91907633773b
-- title:
--   Aether Catalog definitions — Shared_CollisionSchemeUniversalBarrier
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CollisionSchemeUniversalBarrier`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CollisionSchemeUniversalBarrier.lean by skeleton subtraction
import Mathlib

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

namespace CollisionBarrier

open Finset

/-- An abstract collision-based factoring scheme: a finite search space
together with a map assigning a natural number to each search point.  A factor
is extracted from the difference of two values. -/
structure Scheme (α : Type*) where
  /-- The finite search space (its cardinality is the scheme's cost). -/
  space : Finset α
  /-- The value (residue representative, tuple sum, evaluation …) at a point. -/
  val : α → ℕ

variable {α : Type*}

/-- The set of nonnegative pairwise differences produced by a scheme. -/
noncomputable def diffs [DecidableEq α] (C : Scheme α) : Finset ℕ :=
  (C.space ×ˢ C.space).image (fun z => C.val z.1 - C.val z.2)


/-- The scheme *reveals* `f` from `N` if some pairwise difference has
`gcd` equal to `f`. -/
def Reveals [DecidableEq α] (C : Scheme α) (N f : ℕ) : Prop :=
  ∃ d ∈ diffs C, 0 < d ∧ Nat.gcd d N = f

/-! ## The span barrier -/




/-! ## The coverage barrier -/





end CollisionBarrier


