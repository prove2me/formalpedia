-- Prove2me | Definitions.Def_Logic_TimeTravelRecurrence
-- name    : Logic_TimeTravelRecurrence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:08:15.317089+00:00
-- url     : https://prove2.me/theorems/24928e65-4437-433a-8cb3-b57a076f5ee4
-- title:
--   Aether Catalog definitions — Logic_TimeTravelRecurrence
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.TimeTravelRecurrence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/TimeTravelRecurrence.lean by skeleton subtraction
import Mathlib
/-
# Time-Travel Logic II: Recurrence, Parity, and Coordinate-Invariance of Causal Loops

A second layer on the theory of closed timelike curves (CTCs) and the Novikov
self-consistency principle.  The first development modelled a causal loop by its
*loop map* `evolve : S → S` — the net effect of one traversal of a closed
timelike curve — and identified self-consistency with the existence of a fixed
point, giving positive guarantees (monotone loops via Knaster–Tarski, continuous
loops on the unit phase interval via the intermediate value theorem, involutive
loops of odd order).

Here we go deeper along four independent axes, each a genuinely new structural
principle for causal loops:

* **Coordinate invariance** (`selfConsistent_conj`): self-consistency is a
  property of the loop *up to change of world-coordinates*.  A relabelling of the
  state space by a bijection cannot create or destroy a consistent history.  This
  is the statement that the Novikov principle is intrinsic, not an artefact of a
  choice of coordinates.

* **Composability** (`selfConsistent_prod`): a loop acting independently on two
  decoupled subsystems is self-consistent exactly when each subsystem is, so
  consistency is compositional across a product world.

* **Discrete recurrence** (`loop_recurrent`, `loop_universally_consistent`): on a
  *finite* phase space every invertible loop is recurrent — each world-state
  returns to itself after finitely many traversals — and, more strongly, a single
  number of traversals `N` returns *every* state simultaneously.  This is a
  discrete Poincaré recurrence theorem: even a paradoxical loop, iterated enough
  times, becomes universally self-consistent.  It bridges the fixed-point picture
  with finite group theory (the order of the induced permutation).

* **A parity law for time-reversal loops** (`involution_fixedPoints_parity`): for
  an involutive loop (traversing twice restores the world) on a finite phase
  space, the number of self-consistent states has the *same parity* as the size
  of the phase space — a Lefschetz-style mod-2 index.  The odd-order guarantee of
  the first development is the immediate corollary that an odd phase space forces
  at least one consistent history.

The analytic guarantee is also sharpened from the unit interval to an arbitrary
compact phase interval `[a,b]` (`continuous_selfConsistent_Icc`).

The four axes converge on the grandfather paradox: it is fixed-point-free
(`grandfather_paradoxical`), yet on the two-state phase space it is recurrent with
period two (`grandfather_recurrent`), so *two* traversals of the grandfather loop
are universally self-consistent — the multiverse is not needed to tame a paradox,
only patience.
-/


namespace TimeTravelDeep

open Function

variable {S : Type*}

/-! ## Core model (recalled)

A **causal loop** is recorded by its loop map `evolve : S → S`; the loop is
*self-consistent* when some world-state is reproduced by one traversal. -/

/-- A **causal loop** (closed timelike curve): `evolve s` is the world-state that
results from feeding the state `s` once around the loop. -/
structure CausalLoop (S : Type*) where
  /-- The net effect of one traversal of the loop on the world-state. -/
  evolve : S → S

/-- **Novikov self-consistency principle.** A loop is self-consistent when some
world-state is reproduced by one traversal, i.e. a history compatible with itself. -/
def SelfConsistent (L : CausalLoop S) : Prop := ∃ s, L.evolve s = s

/-- The **iterated loop**: traversing the loop `n` times in succession. -/
def iterate (L : CausalLoop S) (n : ℕ) : CausalLoop S := ⟨L.evolve^[n]⟩


/-- A loop map is **paradoxical** if no world-state is left unchanged: every
history contradicts itself (the grandfather situation). -/
def Paradoxical (f : S → S) : Prop := ∀ s, f s ≠ s

/-! ## Coordinate invariance

Self-consistency is intrinsic to the loop: it survives any bijective relabelling
of the world-states. -/


/-! ## Composability across a product world -/


/-! ## Discrete Poincaré recurrence on a finite phase space -/




/-! ## A parity law for time-reversal (involutive) loops -/



/-! ## Sharpened analytic guarantee on an arbitrary phase interval -/


/-! ## Convergence on the grandfather paradox -/




/-! ## Examples and sanity checks -/

-- The identity loop is self-consistent (everyone is their own consistent history).
-- The grandfather loop is *not* self-consistent in a single traversal.
end TimeTravelDeep

/-
-- !-- Lab Notes -- !--

Hypothesis (Hypothesizer).  Five conjectures about causal loops beyond the
fixed-point existence layer:
  (H1) Self-consistency is invariant under bijective relabelling of world-states
       — the Novikov principle is coordinate-free.
  (H2) Self-consistency is compositional across a product of decoupled subsystems.
  (H3) [BOLD] On a finite phase space, every invertible loop is recurrent, and in
       fact universally recurrent: one common number of traversals returns every
       state (a discrete Poincaré recurrence bridging fixed points and the finite
       group generated by the loop).
  (H4) [BOLD] For an involutive (time-reversal) loop on a finite phase space, the
       count of self-consistent states equals the phase-space size mod 2 — a
       Lefschetz-style parity index generalising the odd-order guarantee.
  (H5) The analytic (Brouwer/IVT) guarantee holds on every compact phase
       interval, not only the unit interval.

Experiment (Experimenter).  All five were proved.  H3 uses the permutation induced
by an invertible loop on a finite set: its order N > 0 satisfies loopᴺ = id, so
loopᴺ fixes every state; per-state recurrence is the specialisation.  H4 follows
from the evenness of the support of an involution (its non-fixed points pair up),
so |phase space| - |fixed points| is even.  H5 reruns the sub/IVT argument on an
arbitrary [a,b].  H1, H2 are direct fixed-point transport arguments.

Analysis (Analyst).  Structural pattern: the four principles are the four natural
symmetries/operations one can impose on a loop map — relabelling (H1), product
(H2), iteration on a finite carrier (H3), and the involution constraint (H4).
Recurrence (H3) is the deepest: it shows paradox is a *single-traversal*
phenomenon; every invertible loop on a finite world is eventually self-consistent.
The grandfather loop is the sharp witness — paradoxical yet period-two recurrent.

Critique (Critic).  Guardrails checked: no theorem is `True`/definitional; the
parity law is proved by a genuine combinatorial argument (support evenness), not
`decide`; recurrence uses `orderOf`/group theory, not brute force.  Boundary:
recurrence needs invertibility (a non-injective loop can be strictly eventually
periodic without returning, e.g. a constant map has no positive iterate equal to
the identity unless the space is a point) and finiteness (translation on the
integers is invertible but not recurrent).  The parity law needs the involution
hypothesis: a general permutation can have fixed-point count of either parity.

Synthesis (Principal Investigator).  Self-consistency of causal loops is
coordinate-free, compositional, generically achievable by iteration on finite
worlds, and parity-controlled for time-reversal loops.  Paradox is confined to a
single traversal on finite invertible worlds.  See FUTURE_DIRECTIONS.md.
-/


