-- Prove2me | Definitions.Def_Shared_SmoothCountSparsity
-- name    : Shared_SmoothCountSparsity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:05:48.443513+00:00
-- url     : https://prove2.me/theorems/8962d684-340f-48ee-882e-a3080686589c
-- title:
--   Aether Catalog definitions — Shared_SmoothCountSparsity
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.SmoothCountSparsity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/SmoothCountSparsity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_NumberTheory_IsSmooth

/-!
# Rigorous sparsity of the smooth pool, from the exponent-vector injection

Context (experiment 465, paper 130).  The quadratic sieve needs `B`-smooth values
`x^2 - N`; the whole subexponential run time is a trade-off between the *size* of
the factor base (`π(B)` relations must be collected) and the *rarity* of smooth
values.  Everything asymptotic about that trade-off is Dickman heuristics; this
file records the part that is an unconditional theorem, and which is the true
reason the smooth pool is thin at fixed `B`:

> a `B`-smooth number `n ≤ x` is *determined* by its exponent vector, whose
> entries are at most `log₂ x`, so there are at most `(log₂ x + 1) ^ π(B)` of
> them — polylogarithmic in `x` for fixed `B`.

This is the finite, unconditional skeleton underneath the `ρ(u)` model: it forces
`B → ∞` with `x`, which is what makes the sieve subexponential rather than
polynomial.  It is proved here by an explicit injection of the smooth pool into
the space of exponent vectors, using the catalog predicate `isSmooth` of
`Catalog.Shared.NumberTheory.IsSmooth`.

Main results:

* `mem_smoothPool_iff` — the decidable pool predicate agrees with the catalog
  predicate `isSmooth`.
* `factorization_le_log_two` — every exponent of a number `≤ x` is `≤ log₂ x`.
* `smoothPool_card_le` — `Ψ(x,B) ≤ (log₂ x + 1) ^ π(B)`.
* `smoothPool_card_le_pow_pi` — the same bound with the factor base written as
  the prime-counting function.
* `smoothPool_one` — the extreme case `B = 1`: only `n = 1` is `1`-smooth.
-/

namespace SmoothSparsity

open Finset

/-- The factor base: primes `p ≤ B`. -/
def factorBase (B : ℕ) : Finset ℕ := (Finset.range (B + 1)).filter Nat.Prime

/-- The smooth pool `Ψ(x,B)` as a finset: the `B`-smooth integers in `[1, x]`. -/
def smoothPool (B x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun n => ∀ p ∈ n.primeFactors, p ≤ B)







end SmoothSparsity


