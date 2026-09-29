-- Prove2me | solution 1 for SmoothSparsity.smoothPool_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:54:06.212508+00:00
-- url     : https://prove2.me/submissions/2cd2c732-7146-4a70-b07b-4f032f16057a

-- Sol generated from Shared/SmoothCountSparsity.lean
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










open SmoothSparsity in
theorem solution(x : ℕ) (hx : 1 ≤ x) : smoothPool 1 x = {1} := by
  ext n
  simp only [smoothPool, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    by_contra hne
    have hn : 2 ≤ n := by omega
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
    have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpd, by omega⟩
    have := h3 p hmem
    have := hp.two_le
    omega
  · rintro rfl
    simp [hx]
