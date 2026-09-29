-- Prove2me | Definitions.Def_Shared_QSRelationPoolRandom
-- name    : Shared_QSRelationPoolRandom
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:05:07.585689+00:00
-- url     : https://prove2.me/theorems/1d712c8a-27e1-4a5b-9f5d-95c40b36131a
-- title:
--   Aether Catalog definitions — Shared_QSRelationPoolRandom
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.QSRelationPoolRandom`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/QSRelationPoolRandom.lean by skeleton subtraction
import Mathlib

/-!
# The quadratic-sieve relation pool is *exactly* random-equivalent, prime by prime

Context (experiment 465, paper 130).  In the quadratic sieve one factors the
values `v(x) = x^2 - N` over a factor base of primes `p ≤ B`, and one models the
probability that `v(x)` is `B`-smooth by the probability that a *random* integer
of the same size is `B`-smooth.  This looks suspicious, because the values
`x^2 - N` are **not** random: an odd prime `p ∤ N` can divide `x^2 - N` only when
`N` is a quadratic residue mod `p`, i.e. only *half* the primes are admissible at
all.  The empirical finding of the experiment is that, nevertheless, the pool
behaves exactly like a random pool of the same size at every scale tested
(`N ∈ {2^32 .. 2^44}`, ratio `0.993–1.020`).

This file proves the exact algebraic identity that *explains* that measurement:

* only half of the nonzero residues `N` are admissible
  (`card_admissible_residues`), but
* each admissible prime hits **twice** as often per period
  (`root_count_of_isSquare`), and
* the two effects cancel **exactly**, not just to leading order
  (`relation_pool_random_equivalent`, `expected_hits_eq_one`):
  the average, over the residue of `N`, of the number of `x` per period `p` with
  `p ∣ x^2 - N` is exactly `1` — the same as for a random integer sequence.

Main results:

* `dvd_qsValue_iff_sq_eq` — the arithmetic of the pool transported to `ZMod p`.
* `isSquare_of_dvd_qsValue` — the quadratic-character constraint on divisors.
* `exists_dvd_qsValue_iff_isSquare` — the constraint is *exactly* the obstruction.
* `root_count_of_isSquare` / `root_count_of_not_isSquare` — the `2`/`0` dichotomy.
* `card_admissible_residues` — exactly `(p-1)/2` admissible nonzero residues.
* `relation_pool_random_equivalent` — the exact cancellation `2 · (p-1)/2 = p-1`.
* `expected_hits_eq_one` — total hit count over a full period of residues is `p`.
-/

namespace QSRelationPool

open Finset

/-- The quadratic-sieve value at `x` for the modulus `N`: `v(x) = x^2 - N`. -/
def qsValue (N x : ℤ) : ℤ := x ^ 2 - N

/-- Number of `x` in one period mod `p` for which `p` divides the sieve value,
i.e. the number of square roots of `N` in `ZMod p`. -/
noncomputable def rootCount (p : ℕ) [Fact p.Prime] (a : ZMod p) : ℕ :=
  {x : ZMod p | x ^ 2 = a}.toFinset.card

/-! ## Transporting the pool to `ZMod p` -/




/-! ## The `2`/`0` dichotomy for the local hit count -/

variable {p : ℕ} [Fact p.Prime]





/-! ## The exact cancellation -/


/-- The admissible nonzero residues: those `a` for which some sieve value is
divisible by `p`. -/
noncomputable def admissible (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  {a : ZMod p | a ≠ 0 ∧ IsSquare a}.toFinset



/-! ## Lab notes: machine-checked instances of the identities

The following finite checks are verified by the kernel (`decide`), and are the
small-scale instances of the theorems above; they reproduce, exactly, the
`hitcounts ∈ {0,1,2}`, `#admissible = (p-1)/2`, `total = p` pattern measured
numerically in `ComputationalEvidence.md` for `p = 7, 11, 13, 17, 19, 31`. -/

section LabNotes

end LabNotes

end QSRelationPool


