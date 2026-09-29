-- Prove2me | solution 1 for Novelty.TraceProfile.two_ne_zero_zmod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:26:43.02751+00:00
-- url     : https://prove2.me/submissions/66f7166d-96cc-4edd-88a9-1097c996fa74

-- Sol generated from Novelty/TraceProfileTraceSet.lean
import Mathlib
import Definitions.Def_Novelty_TraceProfileTraceSet
/-
# TRACEPROFILE II — the trace set: exact size and one bit per prime

Phase A research file (Novelty domain), Paper 50 / Experiment 385.

For a finite commutative ring `R` and `N : R` the **trace set** is

`S_R(N) = {x + y : x * y = N}`,

the set of all residues that the trace `s = p + q` of a factorisation of `N` can
possibly take.  The experiment measured `|S_{ZMod m}(N)| = (m+1)/2` for odd primes
`m`, and the *joint law* `|S_{ZMod M#}(N)| / M# = 2^{-ω(M#)}` ("exactly one bit per
prime, additively independent").

This file proves the exact statements.

## Main results

* `mem_traceSet` — the defining membership criterion.
* `card_traceSet_ringEquiv` — the trace set is a ring-isomorphism invariant.
* `traceSet_prod` / `card_traceSet_prod` — the trace set of a product ring is the
  product of the trace sets: **CRT multiplicativity**.
* `card_traceSet_zmod_mul` — the arithmetic CRT form for coprime moduli.
* `card_traceSet_prime` — **the exact size over a prime field**:
  `2 * |S_p(N)| = p + 1` if `N` is a nonzero square mod `p`, and `p - 1` otherwise.
  (This *refines* the experimental reading `(m+1)/2`: the true value is
  `(m + χ(N))/2` with `χ` the quadratic character — a `±1` correction invisible at
  the measured precision, but it is the exact law.)
* `traceNat_primorial` — multiplicativity along a squarefree modulus.
* `traceNat_one_bit_per_prime` — **the joint law**:
  `∏ (p-1) ≤ 2^{ω} * |S_{M}(N)| ≤ ∏ (p+1)` for `M = ∏ p` squarefree odd,
  i.e. the trace set has density `2^{-ω(M)}` up to the `(1 ± 1/p)` corrections.
* `card_traceSet_lt_prime` — the trace really is constrained: over a prime field the
  trace set is a proper subset (about half the residues).
-/


open Novelty.TraceProfile

open Finset

/-! ## The trace set of a finite commutative ring -/

variable {R S : Type*} [CommRing R] [Fintype R] [DecidableEq R]
  [CommRing S] [Fintype S] [DecidableEq S]






/-! ## CRT multiplicativity -/




/-! ## The exact size over a prime field -/


variable {q : ℕ} [hq : Fact (Nat.Prime q)]








/-! ## The joint law: one bit per prime

To speak about a varying modulus we use the `Set.ncard` version of the trace-set
size, a *total* function of the modulus (no finiteness instance required). -/










open Novelty.TraceProfile in
theorem solution(hq2 : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
  have hd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).1 h2
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1
  · exact hq.out.one_lt.ne' h1
  · exact hq2 h1
