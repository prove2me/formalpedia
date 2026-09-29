-- Prove2me | Theorems.Thm_Novelty_TraceProfile_card_candidates_ge
-- name    : Novelty.TraceProfile.card_candidates_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:17:05.927437+00:00
-- url     : https://prove2.me/theorems/12f3eb2b-9ae6-41e2-98a1-7efdbba6c9cf
-- title:
--   A residue *set* `S` modulo `M` leaves at least `|S| · (N/M - 1)` candidates in the
-- statement:
--   A residue *set* `S` modulo `M` leaves at least `|S| · (N/M - 1)` candidates in the
--   window `[1, N]`.
--
--   ```lean
--   theorem Novelty.TraceProfile.card_candidates_ge(M N : ℕ) [NeZero M] (S : Finset (ZMod M)) :
--       S.card * (N / M - 1) ≤ ((Finset.Icc 1 N).filter (fun t : ℕ => (t : ZMod M) ∈ S)).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/TraceProfilePinningBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/TraceProfilePinningBarrier.lean#L85

-- Thm stub generated from Novelty/TraceProfilePinningBarrier.lean
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

theorem Novelty.TraceProfile.card_candidates_ge(M N : ℕ) [NeZero M] (S : Finset (ZMod M)) :
    S.card * (N / M - 1) ≤ ((Finset.Icc 1 N).filter (fun t : ℕ => (t : ZMod M) ∈ S)).card := by sorry
