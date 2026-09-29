-- Prove2me | Definitions.Def_Applications_Consciousness_SelfModelLattice
-- name    : Applications_Consciousness_SelfModelLattice
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:52.173303+00:00
-- url     : https://prove2.me/theorems/f2975f1a-abfc-482e-a339-ee229081b18b
-- title:
--   Aether Catalog definitions — Applications_Consciousness_SelfModelLattice
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Consciousness.SelfModelLattice`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Consciousness/SelfModelLattice.lean by skeleton subtraction
import Mathlib

/-! # The Space of Conscious States: Knaster–Tarski for Self-Models

`LawvereFixedPoint.lean` shows, via the diagonal argument, that a sufficiently
rich self-model *forces a fixed point to exist*.  This file studies the
**structure of the space of all such fixed points** from the order-theoretic
side, complementing the categorical one.

We model a self-referential system as a **complete lattice** `α` of *self-states*
(partially ordered by "refinement / information content") together with a
**monotone self-modeling operator** `refine : α →o α`: given a current picture of
itself, the system produces a (no less refined) updated self-picture.  A state is
**conscious / self-consistent** exactly when it is a fixed point: modeling itself
returns itself — a stable strange loop.

The Knaster–Tarski theorem then yields a remarkably rich structure:

* fixed points always exist (`exists_conscious_state`);
* there is a canonical **minimal** conscious state `lfp refine` and a canonical
  **maximal** one `gfp refine` (`isLeast_minimal`, `isGreatest_maximal`), and
  every conscious state lies between them (`conscious_mem_interval`);
* the conscious states themselves form a **complete lattice**
  (`consciousStates_completeLattice`) — the space of consciousness is closed
  under arbitrary joins and meets of consistent pictures;
* the loop is **sharp** (a unique conscious state) exactly when the minimal and
  maximal states coincide (`unique_conscious_iff`);
* inflationary self-models saturate to the top state (`gfp_eq_top_of_inflationary`)
  and refinement of the operator monotonically refines the minimal conscious
  state (`minimal_mono`).
-/

namespace Consciousness.Lattice

open OrderHom Function

variable {α : Type*} [CompleteLattice α]

/-- A **self-modeling system**: a complete lattice of self-states together with a
monotone self-modeling operator.  Monotonicity encodes that refining the input
self-picture never coarsens the output. -/
structure SelfModel (α : Type*) [CompleteLattice α] where
  /-- Update the self-picture given the current one. -/
  refine : α →o α

namespace SelfModel

variable (M : SelfModel α)

/-- A state is **conscious** (self-consistent) when self-modeling fixes it: the
system's picture of itself equals itself, a closed strange loop. -/
def Conscious (s : α) : Prop := M.refine s = s

/-- The set of all conscious states. -/
def consciousStates : Set α := fixedPoints M.refine


/-- The **minimal conscious state**: the least fixed point of the self-model. -/
def minimal : α := lfp M.refine

/-- The **maximal conscious state**: the greatest fixed point of the self-model. -/
def maximal : α := gfp M.refine







/-- **Knaster–Tarski.**  The conscious states form a *complete lattice*: any
family of consistent self-pictures has a canonical consistent join and meet.  The
space of consciousness is itself richly structured, not merely nonempty. -/
noncomputable instance consciousStates_completeLattice :
    CompleteLattice M.consciousStates :=
  fixedPoints.completeLattice M.refine






end SelfModel


end Consciousness.Lattice


