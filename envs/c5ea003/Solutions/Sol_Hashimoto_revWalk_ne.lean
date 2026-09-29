-- Prove2me | solution 1 for Hashimoto.revWalk_ne
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:43:03.263476+00:00
-- url     : https://prove2.me/submissions/016a59e4-2a2d-458b-a877-e8af29d2c3f8

-- Sol generated from Algebra/NonBacktracking/ReversalParity.lean
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Definitions.Def_Algebra_NonBacktracking_ReversalParity
import Theorems.Thm_Hashimoto_mem_closedNBWalks

/-!
# Reversal of non-backtracking walks and parity of the trace

Reversing a walk and flipping each of its darts is an involution on the set of rooted
closed non-backtracking walks. It has **no fixed point**: the root of the reversed walk
is the reversal of the root, and a dart is never equal to its own reversal. Consequently

`trace (B ^ n)` is even for every `n`.

For `n = 0` this recovers the classical handshake statement (the number of darts is even);
for `n ≥ 1` it says that closed non-backtracking walks come in genuinely distinct
clockwise/anticlockwise pairs.

## Main results

* `Hashimoto.even_card_of_involution` — a finset carrying a fixed-point-free involution
  has even cardinality (proved by summing the constant `1` over `ZMod 2`).
* `Hashimoto.revWalk_mem` — reversal preserves rooted closed non-backtracking walks.
* `Hashimoto.even_trace_hashimoto_pow` — `Even (trace (B ^ n))`.
-/

open Finset SimpleGraph List

open Hashimoto

/-! ## A parity tool -/


/-! ## Reversal of dart walks -/

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]







/-! ## The reversal intertwiner -/





open Hashimoto in
theorem solution{n : ℕ} {l : List G.Dart} (hl : l ∈ closedNBWalks G n) :
    revWalk l ≠ l := by
  rw [mem_closedNBWalks] at hl
  obtain ⟨hlen, -, hend⟩ := hl
  have hne : l ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  obtain ⟨d, hd⟩ : ∃ d, l.head? = some d := by
    cases l with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨a, rfl⟩
  intro hEq
  have hhead : (revWalk l).head? = some d.symm := by
    rw [revWalk, List.head?_reverse, List.getLast?_map, ← hend, hd]
    rfl
  rw [hEq, hd] at hhead
  exact SimpleGraph.Dart.symm_ne d (by simpa using hhead.symm)
