-- Prove2me | solution 1 for Novelty.TraceProfile.traceNat_one_bit_per_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:47:26.815866+00:00
-- url     : https://prove2.me/submissions/38bd4bfc-6a4a-4f5a-b037-200a8a99a900

-- Sol generated from Novelty/TraceProfileTraceSet.lean
import Mathlib
import Definitions.Def_Novelty_TraceProfileTraceSet
import Theorems.Thm_Novelty_TraceProfile_card_traceSet_prime
import Theorems.Thm_Novelty_TraceProfile_traceNat_eq_card
import Theorems.Thm_Novelty_TraceProfile_traceNat_primorial
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





open scoped Classical in
/-- **The exact size over a prime modulus**, in the `traceNat` normalisation:
`2 |S_p(N)| = p + χ_p(N)` with `χ` the quadratic character. -/
theorem two_mul_traceNat_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) (hdvd : ¬ p ∣ N) :
    2 * traceNat p N = if IsSquare ((N : ZMod p)) then p + 1 else p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [traceNat_eq_card]
  have h := card_traceSet_prime hp2 ((N : ZMod p))
    (fun h => hdvd ((ZMod.natCast_eq_zero_iff N p).1 h))
  convert h using 2





open Novelty.TraceProfile in
theorem solution(P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (h2 : ∀ p ∈ P, p ≠ 2) (N : ℕ) (hN : ∀ p ∈ P, ¬ (p ∣ N)) :
    (∏ p ∈ P, (p - 1)) ≤ 2 ^ P.card * traceNat (∏ p ∈ P, p) N ∧
      2 ^ P.card * traceNat (∏ p ∈ P, p) N ≤ ∏ p ∈ P, (p + 1) := by
  classical
  have hkey : 2 ^ P.card * traceNat (∏ p ∈ P, p) N = ∏ p ∈ P, (2 * traceNat p N) := by
    rw [traceNat_primorial N P hP, Finset.prod_mul_distrib, Finset.prod_const]
  have hbound : ∀ p ∈ P, 2 * traceNat p N
      = if IsSquare ((N : ZMod p)) then p + 1 else p - 1 :=
    fun p hp => two_mul_traceNat_prime (hP p hp) (h2 p hp) N (hN p hp)
  refine ⟨?_, ?_⟩ <;> rw [hkey] <;> refine Finset.prod_le_prod' (fun p hp => ?_) <;>
      rw [hbound p hp] <;> by_cases hs : IsSquare ((N : ZMod p)) <;> simp [hs] <;> omega
