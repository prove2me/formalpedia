-- Prove2me | solution 1 for Hashimoto.forall2_ne_rotate_two_of_nodup
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T20:24:52.362333+00:00
-- url     : https://prove2.me/submissions/d1883530-1795-409d-9207-a2b712d3fef3

-- Sol generated from Algebra/NonBacktracking/CyclePositivity.lean
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_VertexCycles

/-!
# Cycles make the non-backtracking trace positive

The trace formula turns a purely graph-theoretic statement — "`G` contains a cycle" —
into an algebraic one about the Hashimoto matrix `B`.

## Main results

* `Hashimoto.one_le_trace_of_nodup_cyclic` — a closed cyclically adjacent vertex word of
  length at least three with distinct letters contributes a rooted closed
  non-backtracking walk, so `1 ≤ trace (B ^ m)`.
* `Hashimoto.one_le_trace_of_isCycle` — every cycle of length `m` in `G` forces
  `1 ≤ trace (B ^ m)`.
* `Hashimoto.isAcyclic_of_trace_eq_zero` — conversely, if all traces `trace (B ^ n)`
  vanish for `n ≥ 1` then `G` is acyclic. Together with `Hashimoto.trace_hashimoto_pow`
  this says: the non-backtracking trace sequence detects the presence of cycles.
-/

open Finset SimpleGraph List

open Hashimoto

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Distinct letters give no backtracking -/



/-! ## From cycles in the graph -/







open Hashimoto in
omit [Fintype V] [DecidableEq V] in
theorem solution{u : List V} (h3 : 3 ≤ u.length) (hnd : u.Nodup) :
    Forall₂ (· ≠ ·) (u.rotate 2) u := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, ?_⟩
  intro i h₁ h₂ hEq
  rw [List.get_rotate] at hEq
  rw [hnd.get_inj_iff] at hEq
  have hmod : (i + 2) % u.length = i := by simpa [Fin.ext_iff] using hEq
  rcases lt_or_ge (i + 2) u.length with h | h
  · rw [Nat.mod_eq_of_lt h] at hmod; omega
  · have hsub : (i + 2) % u.length = i + 2 - u.length := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega
