-- Prove2me | Definitions.Def_Novelty_TraceProfileTraceSet
-- name    : Novelty_TraceProfileTraceSet
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:44:01.641354+00:00
-- url     : https://prove2.me/theorems/3adf9cf1-5bc1-4fea-b1f6-9938dc3b22d1
-- title:
--   Aether Catalog definitions — Novelty_TraceProfileTraceSet
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.TraceProfileTraceSet`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/TraceProfileTraceSet.lean by skeleton subtraction
import Mathlib
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


namespace Novelty.TraceProfile

open Finset

/-! ## The trace set of a finite commutative ring -/

variable {R S : Type*} [CommRing R] [Fintype R] [DecidableEq R]
  [CommRing S] [Fintype S] [DecidableEq S]

/-- All ordered factorisations of `N` inside `R`. -/
def factorPairs (N : R) : Finset (R × R) := univ.filter (fun z => z.1 * z.2 = N)

/-- The **trace set** `{x + y : x*y = N}` of `N` in a finite commutative ring. -/
def traceSet (N : R) : Finset R := (factorPairs N).image (fun z => z.1 + z.2)




/-! ## CRT multiplicativity -/




/-! ## The exact size over a prime field -/

section Prime

variable {q : ℕ} [hq : Fact (Nat.Prime q)]







end Prime

/-! ## The joint law: one bit per prime

To speak about a varying modulus we use the `Set.ncard` version of the trace-set
size, a *total* function of the modulus (no finiteness instance required). -/

open scoped Classical in
/-- The size of the trace set of `N` modulo `m`, as a total function of `m`. -/
noncomputable def traceNat (m N : ℕ) : ℕ :=
  {s : ZMod m | ∃ x y : ZMod m, x * y = (N : ZMod m) ∧ x + y = s}.ncard








end Novelty.TraceProfile


