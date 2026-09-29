-- Prove2me | solution 1 for Novelty.TraceProfile.card_traceSet_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:31:58.934851+00:00
-- url     : https://prove2.me/submissions/babda0c0-fbf9-468e-8e8a-1c5ca9090383

-- Sol generated from Novelty/TraceProfileTraceSet.lean
import Mathlib
import Definitions.Def_Novelty_TraceProfileTraceSet
import Theorems.Thm_Novelty_TraceProfile_card_degenerate_traces
import Theorems.Thm_Novelty_TraceProfile_fiber_card
import Theorems.Thm_Novelty_TraceProfile_traceSet_eq_image_nonzero
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
    2 * (traceSet N).card = if IsSquare N then q + 1 else q - 1 := by
  classical
  have hq3 : 3 ≤ q := by
    have h2 := hq.out.two_le
    omega
  set A : Finset (ZMod q) := univ.filter (fun x : ZMod q => x ≠ 0) with hA
  have hAcard : A.card = q - 1 := by
    have hAe : A = univ.erase (0 : ZMod q) := by
      ext x; simp [hA, Finset.mem_erase]
    rw [hAe, Finset.card_erase_of_mem (mem_univ 0), Finset.card_univ, ZMod.card]
  have himg : traceSet N = A.image (fun x => x + N * x⁻¹) := traceSet_eq_image_nonzero N hN
  have hsum := Finset.card_eq_sum_card_image (fun x : ZMod q => x + N * x⁻¹) A
  rw [hAcard, ← himg] at hsum
  have hsum2 : q - 1 = ∑ s ∈ traceSet N, (if s ^ 2 = 4 * N then 1 else 2) := by
    rw [hsum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    exact fiber_card N s hN hs
  have hsplit : ∑ s ∈ traceSet N, (if s ^ 2 = 4 * N then 1 else 2)
      = ((traceSet N).filter (fun s => s ^ 2 = 4 * N)).card
        + 2 * ((traceSet N).filter (fun s => ¬ s ^ 2 = 4 * N)).card := by
    rw [Finset.sum_ite]
    simp [Finset.sum_const, mul_comm]
  have hcards : ((traceSet N).filter (fun s => s ^ 2 = 4 * N)).card
      + ((traceSet N).filter (fun s => ¬ s ^ 2 = 4 * N)).card = (traceSet N).card :=
    Finset.card_filter_add_card_filter_not _
  have hdeg := card_degenerate_traces hq2 N hN
  rw [hsplit] at hsum2
  by_cases hsq : IsSquare N
  · rw [if_pos hsq] at hdeg
    rw [hdeg] at hsum2
    rw [if_pos hsq]
    omega
  · rw [if_neg hsq] at hdeg
    rw [hdeg] at hsum2
    rw [if_neg hsq]
    omega
