-- Prove2me | Definitions.Def_Probability_TimeTravelCausalConsistency
-- name    : Probability_TimeTravelCausalConsistency
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:38:54.039999+00:00
-- url     : https://prove2.me/theorems/2ed6e872-25ce-4c19-a64a-3b32dc03fcf5
-- title:
--   Aether Catalog definitions — Probability_TimeTravelCausalConsistency
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.TimeTravelCausalConsistency`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/TimeTravelCausalConsistency.lean by skeleton subtraction
import Mathlib
/-
# Time-Travel Logic: Formalizing Causal Consistency

A self-contained formalization of the logic of closed timelike curves (CTCs) and
time-travel paradoxes.  The central object is the *loop map* `evolve : S → S`,
which records the net effect on the world-state of traversing a closed timelike
curve once.  On top of this we develop, as a connected chain of theorems:

* the **Novikov self-consistency principle** as the existence of a fixed point,
  and its equivalence with the existence of a *closed timelike history*
  (`selfConsistent_iff_closedHistory`);
* the **grandfather paradox** as a fixed-point-free ("paradoxical") loop, proved
  genuinely inconsistent (`grandfather_not_selfConsistent`);
* two positive **consistency guarantees** —
    * monotone loops on a complete lattice are always self-consistent
      (Knaster–Tarski, `monotone_selfConsistent`),
    * continuous loops on a phase interval are always self-consistent
      (1-D Brouwer / IVT, `continuous_selfConsistent`, a toy model of the
      conjecture that Gödel-universe CTCs are self-consistent),
    * involutive loops on a state space of odd size are self-consistent
      (`involutive_odd_selfConsistent`);
* the **many-worlds / branching** resolution: a paradoxical action that admits no
  single-timeline consistent history nevertheless admits a consistent *branching*
  history, because the traveller is sent to a fresh branch rather than forced into
  a contradiction (`branching_resolves_paradox`).

Every theorem is used by a later one, forming a single chain from the definitions
to the branching resolution.
-/


namespace TimeTravel

open Function

variable {S : Type*}

/-! ## Core model -/

/-- A **causal loop** (closed timelike curve): `evolve s` is the world-state that
results from feeding the state `s` once around the loop. -/
structure CausalLoop (S : Type*) where
  /-- The net effect of one traversal of the loop on the world-state. -/
  evolve : S → S

/-- **Novikov self-consistency principle.**  A causal loop is *self-consistent*
when there is a world-state reproduced by one traversal of the loop, i.e. a
history that is compatible with itself. -/
def SelfConsistent (L : CausalLoop S) : Prop := ∃ s, L.evolve s = s


/-! ## Discrete loops and closed timelike histories

A loop `e₁ → e₂ → ⋯ → eₙ → e₁` is presented by its sequence of causal steps
`steps 0, steps 1, …`.  `traverse steps k s` is the world-state after applying the
first `k` steps starting from `s`; the whole length-`n` loop is `traverse steps n`. -/

/-- State after applying the first `k` causal steps, starting from `s`. -/
def traverse (steps : ℕ → S → S) : ℕ → S → S
  | 0, s => s
  | (k + 1), s => steps k (traverse steps k s)



/-- A **closed timelike history** of a length-`n` loop: a labelling `h` of events by
world-states in which every step's cause produces its effect, and the loop closes
(`h n = h 0`). -/
def ClosedHistory (steps : ℕ → S → S) (n : ℕ) (h : ℕ → S) : Prop :=
  (∀ k < n, h (k + 1) = steps k (h k)) ∧ h n = h 0

/-
Auxiliary: iterating `traverse` from a closed history recovers the history.
-/

/-
**Theorem 1 (Novikov ⇔ closed timelike history).**  A length-`n` causal loop is
self-consistent (its evolution `traverse steps n` has a fixed point) iff it admits a
closed timelike history.
-/

/-! ## The grandfather paradox -/

/-- A loop map is **paradoxical** if no world-state is left unchanged by a traversal:
every history contradicts itself. -/
def Paradoxical (f : S → S) : Prop := ∀ s, f s ≠ s

/-
**Theorem 2.**  A paradoxical loop map has no fixed point, hence is not
self-consistent.
-/

/-
The grandfather action on the two-state space `alive/dead`: travelling round the
loop flips the ancestor's status.
-/

/-
**Theorem 3 (grandfather paradox is impossible).**  The grandfather loop admits
no self-consistent history.
-/

/-! ## Positive consistency guarantees -/

/-
**Theorem 4 (monotone loops are always self-consistent — Knaster–Tarski).**
If the state space is a complete lattice and the loop map is monotone, a
self-consistent history always exists.
-/

/-
**Theorem 5 (continuous loops on a phase interval are self-consistent).**  A toy
model of the conjecture that every closed timelike curve in a Gödel universe is
self-consistent: if the loop's evolution is a continuous self-map of the phase
interval `[0,1]`, it has a fixed point (1-D Brouwer, via the intermediate value
theorem).
-/

/-
**Theorem 6 (odd loops are self-consistent).**  If the loop map is an involution
(going round the loop twice restores the state) on a finite state space of odd size,
then it has a fixed point, so the loop is self-consistent.
-/

/-! ## Branching (many-worlds) time travel

Instead of forcing the loop to close, a time traveller is sent to a *fresh branch*.
The multiverse state is `S × ℕ` (world-state together with a branch index); the
branching evolution `branch a` applies the traveller's action `a` and advances to a
new branch. -/

/-- The branching evolution of an action `a`: apply `a` and move to a new branch. -/
def branch (a : S → S) : S × ℕ → S × ℕ := fun p => (a p.1, p.2 + 1)

/-
**Theorem 7 (the traveller always creates a new branch).**  A branching step
always increases the branch index, so it never lands on the same multiverse state:
`branch a` is paradoxical as an ordinary loop map.
-/

/-
A branching history is the concrete sequence of multiverse states visited by the
traveller, one per branch.
-/

/-
**Theorem 8 (branching resolves the paradox).**  For *any* paradoxical action
`a` — one with no single-timeline self-consistent history — the many-worlds model
still admits a fully consistent branching history: the traveller acts freely and is
carried to ever-new branches, producing no contradiction.
-/

/-
**Corollary (grandfather in the multiverse).**  The grandfather action, impossible
in a single timeline, has a consistent branching history: the traveller kills the
ancestor in a new branch and lives on there.
-/

end TimeTravel


