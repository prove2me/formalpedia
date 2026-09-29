-- Prove2me | Theorems.Thm_Novelty_TraceProfile_traceNat_eq_card
-- name    : Novelty.TraceProfile.traceNat_eq_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:18:04.322323+00:00
-- url     : https://prove2.me/theorems/d30e87a5-d8af-4433-b291-8a98b1298488
-- title:
--   TraceNat eq card
-- statement:
--   Formal statement of `Novelty.TraceProfile.traceNat_eq_card` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Novelty.TraceProfile.traceNat_eq_card(m N : ℕ) [NeZero m] :
--       traceNat m N = (traceSet ((N : ZMod m))).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/TraceProfileTraceSet.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/TraceProfileTraceSet.lean#L300

-- Thm stub generated from Novelty/TraceProfileTraceSet.lean
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

theorem Novelty.TraceProfile.traceNat_eq_card(m N : ℕ) [NeZero m] :
    traceNat m N = (traceSet ((N : ZMod m))).card := by sorry
