-- Prove2me | Theorems.Thm_SmoothSparsity_smoothPool_card_le
-- name    : SmoothSparsity.smoothPool_card_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:51:43.863574+00:00
-- url     : https://prove2.me/theorems/db034f11-9be7-4998-a58a-90196784d664
-- title:
--   Sparsity of the smooth pool.
-- statement:
--   **Sparsity of the smooth pool.**  There are at most `(logâ x + 1) ^ Ï(B)`
--   `B`-smooth numbers in `[1, x]`: for a fixed factor base the pool grows only
--   polylogarithmically in `x`.
--
--   ```lean
--   theorem SmoothSparsity.smoothPool_card_le(B x : ℕ) :
--       (smoothPool B x).card ≤ (Nat.log 2 x + 1) ^ (factorBase B).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/SmoothCountSparsity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/SmoothCountSparsity.lean#L83

-- Thm stub generated from Shared/SmoothCountSparsity.lean
import Mathlib
import Definitions.Def_Shared_NumberTheory_IsSmooth
import Definitions.Def_Shared_SmoothCountSparsity

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

open SmoothSparsity

open Finset

theorem SmoothSparsity.smoothPool_card_le(B x : ℕ) :
    (smoothPool B x).card ≤ (Nat.log 2 x + 1) ^ (factorBase B).card := by sorry
