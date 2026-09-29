-- Prove2me | solution 1 for SmoothSparsity.factorization_le_log_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:52:34.959158+00:00
-- url     : https://prove2.me/submissions/7487e47b-81fc-4e84-bd6a-7c1e73fabed7

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
theorem solution{x n p : ℕ} (hn : n ≠ 0) (hx : n ≤ x) :
    n.factorization p ≤ Nat.log 2 x := by
  rcases eq_or_ne (n.factorization p) 0 with h | h
  · simp [h]
  have hmem : p ∈ n.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.2 h
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hmem
  have hx0 : x ≠ 0 := by rintro rfl; omega
  have hdvd : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
  have hple : p ^ n.factorization p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have h2 : 2 ^ n.factorization p ≤ p ^ n.factorization p :=
    Nat.pow_le_pow_left hp.two_le _
  exact (Nat.le_log_iff_pow_le (by norm_num) hx0).2 (le_trans h2 (le_trans hple hx))
