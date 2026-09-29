-- Prove2me | solution 1 for Novelty.TraceProfile.card_residue_class_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:24:48.348985+00:00
-- url     : https://prove2.me/submissions/4844b7b0-8763-434e-8e71-0407158210b9

-- Sol generated from Novelty/TraceProfilePinningBarrier.lean
import Mathlib
import Definitions.Def_Novelty_TraceProfileTraceSet
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
theorem solution(M N : ℕ) [NeZero M] (s : ZMod M) :
    N / M - 1 ≤ ((Finset.Icc 1 N).filter (fun t : ℕ => (t : ZMod M) = s)).card := by
  classical
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  set K := N / M with hK
  rcases Nat.lt_or_ge K 2 with hK2 | hK2
  · omega
  · have hKM : K * M ≤ N := Nat.div_mul_le_self N M
    have hval : s.val < M := ZMod.val_lt s
    have hKM' : (K - 1) * M + M = K * M := by
      have hk1 : K - 1 + 1 = K := by omega
      calc (K - 1) * M + M = (K - 1 + 1) * M := by ring
        _ = K * M := by rw [hk1]
    rw [← Finset.card_range (K - 1)]
    refine Finset.card_le_card_of_injOn (fun k => s.val + (k + 1) * M) ?_ ?_
    · intro k hk
      have hk' : k < K - 1 := Finset.mem_range.mp hk
      have hlow : 1 ≤ s.val + (k + 1) * M := by
        have : 1 * M ≤ (k + 1) * M := Nat.mul_le_mul_right M (by omega)
        omega
      have hhigh : s.val + (k + 1) * M ≤ N := by
        have h2 : (k + 1) * M ≤ (K - 1) * M := Nat.mul_le_mul_right M (by omega)
        omega
      have hcast : (((s.val + (k + 1) * M : ℕ)) : ZMod M) = s := by
        push_cast
        rw [ZMod.natCast_zmod_val]
        simp
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hlow, hhigh⟩, hcast⟩
    · intro a _ b _ hab
      have hab' : s.val + (a + 1) * M = s.val + (b + 1) * M := hab
      have heq : (a + 1) * M = (b + 1) * M := by omega
      have := Nat.eq_of_mul_eq_mul_right hM heq
      omega
