-- Prove2me | Theorems.Thm_TimeTravelDeep_involution_fixedPoints_parity
-- name    : TimeTravelDeep.involution_fixedPoints_parity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:55:59.537291+00:00
-- url     : https://prove2.me/theorems/29175f1f-a2a3-41ff-aee6-18d7c82d07e7
-- title:
--   Parity law for time-reversal loops.
-- statement:
--   **Parity law for time-reversal loops.** For an involutive loop on a finite
--   phase space (traversing twice restores the world), the number of self-consistent
--   world-states has the same parity as the size of the phase space. This is a
--   Lefschetz-style mod-2 fixed-point index.
--
--   ```lean
--   theorem TimeTravelDeep.involution_fixedPoints_parity[Fintype S] [DecidableEq S] (f : S → S)
--       (hf : Involutive f) :
--       Fintype.card {s // f s = s} % 2 = Fintype.card S % 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/TimeTravelRecurrence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/TimeTravelRecurrence.lean#L153

-- Thm stub generated from Logic/TimeTravelRecurrence.lean
import Mathlib
import Definitions.Def_Logic_TimeTravelRecurrence
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


open TimeTravelDeep

open Function

variable {S : Type*}

/-! ## Core model (recalled)

A **causal loop** is recorded by its loop map `evolve : S → S`; the loop is
*self-consistent* when some world-state is reproduced by one traversal. -/






/-! ## Coordinate invariance

Self-consistency is intrinsic to the loop: it survives any bijective relabelling
of the world-states. -/


/-! ## Composability across a product world -/


/-! ## Discrete Poincaré recurrence on a finite phase space -/




/-! ## A parity law for time-reversal (involutive) loops -/

theorem TimeTravelDeep.involution_fixedPoints_parity[Fintype S] [DecidableEq S] (f : S → S)
    (hf : Involutive f) :
    Fintype.card {s // f s = s} % 2 = Fintype.card S % 2 := by sorry
