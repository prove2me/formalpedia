-- Prove2me | solution 1 for Novelty.TraceProfile.card_degenerate_traces
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:28:12.035026+00:00
-- url     : https://prove2.me/submissions/8767a1ca-e34f-4864-ae8d-e9b362d7d584

-- Sol generated from Novelty/TraceProfileTraceSet.lean
import Mathlib
import Definitions.Def_Novelty_TraceProfileTraceSet
import Theorems.Thm_Novelty_TraceProfile_mem_traceSet
import Theorems.Thm_Novelty_TraceProfile_two_ne_zero_zmod
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
theorem solution(hq2 : q ≠ 2) (N : ZMod q) (hN : N ≠ 0) :
    ((traceSet N).filter (fun s => s ^ 2 = 4 * N)).card = if IsSquare N then 2 else 0 := by
  have h2 : (2 : ZMod q) ≠ 0 := two_ne_zero_zmod hq2
  by_cases hsq : IsSquare N
  · rw [if_pos hsq]
    obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr
      exact hN hr
    have hset : (traceSet N).filter (fun s => s ^ 2 = 4 * N) = {2 * r, -(2 * r)} := by
      ext s
      simp only [mem_filter, mem_traceSet, mem_insert, mem_singleton]
      constructor
      · rintro ⟨-, hs2⟩
        have hfac : (s - 2 * r) * (s + 2 * r) = 0 := by
          rw [hr] at hs2
          linear_combination hs2
        rcases mul_eq_zero.1 hfac with h | h
        · exact Or.inl (sub_eq_zero.1 h)
        · right
          linear_combination h
      · rintro (rfl | rfl)
        · exact ⟨⟨r, r, hr.symm, by ring⟩, by rw [hr]; ring⟩
        · exact ⟨⟨-r, -r, by rw [hr]; ring, by ring⟩, by rw [hr]; ring⟩
    rw [hset]
    have hne : (2 * r) ≠ -(2 * r) := by
      intro h
      have : (2 : ZMod q) * (2 * r) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h' | h'
      · exact h2 h'
      · rcases mul_eq_zero.1 h' with h'' | h''
        · exact h2 h''
        · exact hr0 h''
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  · rw [if_neg hsq]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro s -
    intro hs2
    apply hsq
    refine ⟨s * (2 : ZMod q)⁻¹, ?_⟩
    field_simp
    linear_combination -hs2
