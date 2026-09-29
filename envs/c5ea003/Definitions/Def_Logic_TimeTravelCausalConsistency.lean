-- Prove2me | Definitions.Def_Logic_TimeTravelCausalConsistency
-- name    : Logic_TimeTravelCausalConsistency
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:08:17.500653+00:00
-- url     : https://prove2.me/theorems/136761f9-5c95-44ab-8fd2-76dd073f7344
-- title:
--   Aether Catalog definitions — Logic_TimeTravelCausalConsistency
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.TimeTravelCausalConsistency`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/TimeTravelCausalConsistency.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Time-Travel Logic: Formalizing Causal Consistency

This file gives a self-contained formalization of *causal loops* and the
**Novikov self-consistency principle** for time travel.

A **causal loop** is a finite cyclic chain of events

  `e₀ → e₁ → ⋯ → e_{n-1} → e₀`,

where the state of each event causally determines the state of the next.  We
model this by a self-map `step i : X → X` transporting the state of event `i` to
that of event `i+1` (indices taken modulo the loop `length`).

A **consistent history** assigns a state to every event so that every causal step
is respected *and* the assignment is periodic (event `0` really is event `n`).
The **round-trip map** `roundTrip` sends the initial state of event `0` to the
state it acquires after going once around the loop.

The central results are:

* `consistentHistoryEquivFixedPoint` — consistent histories are in canonical
  bijection with fixed points of the round-trip map;
* `novikov_iff_fixedPoint` — the Novikov principle (a consistent history exists)
  holds **iff** the round-trip map has a fixed point;
* `grandfather_paradox` — an explicit loop (the "grandfather paradox", `state ↦
  ¬state`) admits *no* consistent history;
* `roundTrip_iterate` / `pow_roundTrip` — going `k` times around the loop realizes
  the `k`-th iterate of the round-trip map;
* `finite_pow_consistent` — on any finite non-empty state space, some finite number
  of repetitions of the loop *always* has a consistent history (Novikov consistency
  is achievable "in the limit").

Everything is measure-free and purely combinatorial/dynamical.
-/


namespace TimeTravel

variable {X : Type*}

/-- A **causal loop**: `length` events arranged in a cycle, where `step i`
transports the state of event `i` to the state of event `i+1` (indices mod `length`). -/
structure CausalLoop (X : Type*) where
  /-- Number of events in the loop. -/
  length : ℕ
  /-- `step i` sends the state of event `i` to the state of event `i+1`. -/
  step : ℕ → X → X
  /-- A loop has at least one event. -/
  pos : 0 < length

/-- The **trajectory** obtained by starting event `0` in state `x` and applying the
causal steps.  `trajectory x k` is the state produced after `k` causal steps. -/
def CausalLoop.trajectory (L : CausalLoop X) (x : X) : ℕ → X
  | 0 => x
  | (k+1) => L.step (k % L.length) (L.trajectory x k)

/-- The **round-trip map**: the state event `0` returns to after going once around
the loop. -/
def CausalLoop.roundTrip (L : CausalLoop X) (x : X) : X := L.trajectory x L.length

/-- A **consistent history** assigns a state `h k` to every event so that each causal
step is respected and the assignment closes up into a genuine cycle (period `length`).
The Novikov self-consistency principle is the assertion that such a history exists. -/
def CausalLoop.IsConsistentHistory (L : CausalLoop X) (h : ℕ → X) : Prop :=
  (∀ k, h (k+1) = L.step (k % L.length) (h k)) ∧ Function.Periodic h L.length

/-- The loop is **self-consistent** when a consistent history exists. -/
def CausalLoop.SelfConsistent (L : CausalLoop X) : Prop := ∃ h, L.IsConsistentHistory h


lemma traj_succ (L : CausalLoop X) (x : X) (k : ℕ) :
    L.trajectory x (k+1) = L.step (k % L.length) (L.trajectory x k) := rfl

/-- If the round trip fixes `x`, then the trajectory started at `x` is periodic with
period `length`: going around the loop returns every intermediate event to itself. -/
lemma traj_periodic (L : CausalLoop X) {x : X} (hx : L.roundTrip x = x) :
    Function.Periodic (L.trajectory x) L.length := by
  intro k
  induction k with
  | zero => simpa [CausalLoop.roundTrip] using hx
  | succ k ih =>
    rw [show k+1+L.length = (k+L.length)+1 by ring, traj_succ, traj_succ, ih,
      Nat.add_mod_right]

/-- Any consistent history is reconstructed by the trajectory started at its value at
event `0`.  (This direction needs only the causal-step condition, not periodicity.) -/
lemma traj_of_history (L : CausalLoop X) {h : ℕ → X}
    (hh : ∀ k, h (k+1) = L.step (k % L.length) (h k)) (k : ℕ) :
    L.trajectory (h 0) k = h k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [traj_succ, ih, ← hh]

/-- **Main structural theorem.**  The consistent histories of a causal loop are in
canonical bijection with the fixed points of its round-trip map.  A history is
determined by its value at event `0`, which must be a fixed point of the round trip;
conversely every fixed point unrolls to a consistent history via its trajectory. -/
def consistentHistoryEquivFixedPoint (L : CausalLoop X) :
    {h : ℕ → X // L.IsConsistentHistory h} ≃ {x : X // L.roundTrip x = x} where
  toFun h := ⟨h.1 0, by
    have hp := h.2.2 0
    simp only [zero_add] at hp
    have := traj_of_history L h.2.1 L.length
    rw [CausalLoop.roundTrip, this]
    exact hp⟩
  invFun x := ⟨L.trajectory x.1, fun k => traj_succ L x.1 k, traj_periodic L x.2⟩
  left_inv h := by
    apply Subtype.ext
    funext k
    exact traj_of_history L h.2.1 k
  right_inv x := by
    apply Subtype.ext
    rfl



/-! ### The grandfather paradox

The loop with a single event whose causal step negates the state (`state ↦ ¬state`)
is the classic *grandfather paradox*: any consistent state would have to equal its own
negation.  Formally it has no consistent history. -/

/-- The grandfather-paradox loop: one event, causal step `state ↦ ¬state`. -/
def grandfather : CausalLoop Bool where
  length := 1
  step := fun _ b => !b
  pos := one_pos



/-! ### Traversing the loop several times

Going `k` times around the loop is exactly iterating the round-trip map `k` times.
On a finite non-empty state space the round-trip map always has a periodic point, so a
sufficiently repeated loop is *always* consistent, even when a single traversal is not.
-/



/-- The loop traversed `k` times (for `k > 0`); its causal steps are those of `L`
repeated cyclically. -/
def CausalLoop.pow (L : CausalLoop X) (k : ℕ) (hk : 0 < k) : CausalLoop X where
  length := k * L.length
  step := fun i => L.step (i % L.length)
  pos := Nat.mul_pos hk L.pos





end TimeTravel


