-- Prove2me | solution 1 for Novelty.TraceProfile.trace_pinning_barrier
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:50:40.307458+00:00
-- url     : https://prove2.me/submissions/1942a98a-f976-4dd2-94ba-6c7145f81280

-- Sol generated from Novelty/TraceProfilePinningBarrier.lean
import Mathlib
import Definitions.Def_Novelty_TraceProfileTraceSet
import Theorems.Thm_Novelty_TraceProfile_card_candidates_ge
import Theorems.Thm_Novelty_TraceProfile_traceNat_eq_card
import Theorems.Thm_Novelty_TraceProfile_traceNat_one_bit_per_prime
/-
# TRACEPROFILE V — the pinning barrier: why one bit per prime is not a factoring tool

Phase A research file (Novelty domain), Paper 50 / Experiment 385, third research
cycle.

Cycles I–II established the positive half of the trace profile: modulo a squarefree
odd `M = ∏_{p ∈ P} p` coprime to `N`, the trace `s = p + q` of the semiprime is
confined to a set `S_M(N)` of density `2^{-|P|}` (one bit per prime, exactly the
Legendre symbols).  This file proves the negative half — the paper's verdict that
the trace "cannot scale to pin `s`".

The search window for a trace is `[1, N]`: for `p, q ≥ 2` one always has
`p + q ≤ p q = N` (`trace_le_modulus`).  The theorem below counts how many integers
of that window survive *all* the congruence conditions at once:

`2^{|P|} · #{t ≤ N : t mod M ∈ S_M(N)} ≥ (∏_{p ∈ P} (p-1)) · (N/M - 1)`,

i.e. roughly `N / 2^{|P|}` candidates remain.  The congruence data therefore isolates
the trace only when `2^{|P|} ≳ N`, that is `|P| ≳ log₂ N` primes — a modulus
`M = ∏ p` far larger than `N` itself.  One bit per prime is *additive*, while the
search space is *exponential*: the trace is the most accessible residue target and
is still useless for factoring.

## Main results

* `trace_le_modulus` — the search window: `p + q ≤ p q`.
* `card_residue_class_ge` — a congruence class modulo `M` meets `[1, N]` in at least
  `N/M - 1` points.
* `card_candidates_ge` — hence a residue *set* `S` leaves at least `|S|·(N/M - 1)`
  candidates.
* `trace_pinning_barrier` — the combination with the one-bit-per-prime law: the
  surviving-candidate count is at least `(∏ (p-1)) (N/M - 1) / 2^{|P|}`.
* `trace_not_pinned_of_small_modulus` — corollary in the form "two candidates
  survive": no modulus `M ≤ (N-1)/2` can determine the trace.
-/


open Novelty.TraceProfile

open Finset







open Novelty.TraceProfile in
theorem solution(P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (h2 : ∀ p ∈ P, p ≠ 2) (N : ℕ) (hN : ∀ p ∈ P, ¬ (p ∣ N))
    (M : ℕ) [NeZero M] (hM : M = ∏ p ∈ P, p) (B : ℕ) :
    (∏ p ∈ P, (p - 1)) * (B / M - 1)
      ≤ 2 ^ P.card *
        ((Finset.Icc 1 B).filter (fun t : ℕ => (t : ZMod M) ∈ traceSet ((N : ZMod M)))).card := by
  classical
  have hcand := card_candidates_ge M B (traceSet ((N : ZMod M)))
  have hbits := (traceNat_one_bit_per_prime P hP h2 N hN).1
  have hSize : traceNat (∏ p ∈ P, p) N = (traceSet ((N : ZMod M))).card := by
    subst hM
    exact traceNat_eq_card _ N
  rw [hSize] at hbits
  calc (∏ p ∈ P, (p - 1)) * (B / M - 1)
      ≤ (2 ^ P.card * (traceSet ((N : ZMod M))).card) * (B / M - 1) :=
        Nat.mul_le_mul_right _ hbits
    _ = 2 ^ P.card * ((traceSet ((N : ZMod M))).card * (B / M - 1)) := by ring
    _ ≤ 2 ^ P.card * ((Finset.Icc 1 B).filter
          (fun t : ℕ => (t : ZMod M) ∈ traceSet ((N : ZMod M)))).card :=
        Nat.mul_le_mul_left _ hcand
