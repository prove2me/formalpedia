-- Prove2me | Definitions.Def_Shared_SievePolynomialUniversality
-- name    : Shared_SievePolynomialUniversality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:14:31.16685+00:00
-- url     : https://prove2.me/theorems/b2d0ff8a-9837-44c8-ae83-76682226c152
-- title:
--   Aether Catalog definitions — Shared_SievePolynomialUniversality
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.SievePolynomialUniversality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/SievePolynomialUniversality.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_QSRelationPoolRandom

/-!
# Universality of on-average random-equivalence for sieve polynomials

The exact cancellation of `Catalog.Shared.QSRelationPoolRandom` invites the
question: is the quadratic sieve special?  It is not.  This file isolates the
combinatorial skeleton of the phenomenon and shows it is *universal*: for **any**
sieve map `f` on residues (any polynomial, any degree, any modulus), the number
of `x` per period hitting a given target residue averages to exactly
`|domain| / |targets|`, the random-model value.  Averaged over the target, no
sieve polynomial can be better or worse than random.

What the individual polynomial controls is only the *distribution* of that hit
count across targets, and the file characterises exactly when the pool is
random-equivalent target-by-target rather than merely on average:

* `sum_fiber_card` — the averaging identity (universality).
* `pointwise_uniform_iff_bijective` — pointwise random-equivalence holds iff the
  sieve map is a bijection of residues.
* `sq_not_pointwise_uniform` — for `x ↦ x^2` mod an odd prime it fails: the
  hit count is the `2`/`0` dichotomy, never the constant `1`.
* `qs_average_hits_eq_random` — but on average over the modulus residue the
  quadratic sieve hits exactly once per period, like a random sequence.

The moral for the experiment: any measured deviation of the `x^2 - N` pool from
the random control must come from the *interaction across primes* for one fixed
`N`, never from the one-prime statistics, which are pinned by these identities.
-/

namespace SieveUniversality

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

/-- The number of `x` in one period which the sieve map `f` sends to `b`. -/
def hitCount (f : α → β) (b : β) : ℕ := (Finset.univ.filter (fun x => f x = b)).card



/-! ## The quadratic sieve instance -/

variable {p : ℕ} [Fact p.Prime]




end SieveUniversality


