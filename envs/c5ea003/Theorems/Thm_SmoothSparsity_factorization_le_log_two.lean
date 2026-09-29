-- Prove2me | Theorems.Thm_SmoothSparsity_factorization_le_log_two
-- name    : SmoothSparsity.factorization_le_log_two
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:51:31.50558+00:00
-- url     : https://prove2.me/theorems/a49a1dea-5cc6-473f-b076-b0817ade1c92
-- title:
--   Every exponent is small.
-- statement:
--   **Every exponent is small.**  If `0 < n â¤ x` then each exponent in the prime
--   factorisation of `n` is at most `logâ x`.
--
--   ```lean
--   theorem SmoothSparsity.factorization_le_log_two{x n p : ℕ} (hn : n ≠ 0) (hx : n ≤ x) :
--       n.factorization p ≤ Nat.log 2 x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/SmoothCountSparsity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/SmoothCountSparsity.lean#L67

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

theorem SmoothSparsity.factorization_le_log_two{x n p : ℕ} (hn : n ≠ 0) (hx : n ≤ x) :
    n.factorization p ≤ Nat.log 2 x := by sorry
