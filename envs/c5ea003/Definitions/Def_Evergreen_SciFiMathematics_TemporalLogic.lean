-- Prove2me | Definitions.Def_Evergreen_SciFiMathematics_TemporalLogic
-- name    : Evergreen_SciFiMathematics_TemporalLogic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:40:15.296448+00:00
-- url     : https://prove2.me/theorems/6fccfc4a-d09f-4b90-9a47-a2e9f6a27e06
-- title:
--   Aether Catalog definitions — Evergreen_SciFiMathematics_TemporalLogic
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.SciFiMathematics.TemporalLogic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/SciFiMathematics/TemporalLogic.lean by skeleton subtraction
import Mathlib
/-
# Mathematics of Science Fiction — Chapter 11: Temporal Logic and Causality

Formalized proofs about partial orders, causal structures, and the
mathematical foundations of time in science fiction.
-/

namespace SciFiMathematics.TemporalLogic

/-! ## Section 11.1: Causal Ordering

A causal structure is a partial order on events. Time travel requires
weakening this to a preorder. -/

/-
In a partial order, there are no non-trivial cycles.
    This is the mathematical statement that time travel is impossible
    in a strictly causal universe.
-/

/-
A strict partial order (modeling strict causality) has no self-loops.
    No event can strictly cause itself.
-/

/-! ## Section 11.2: Branching Time

In a branching time structure, the past is linear but the future may branch.
This is the mathematical model for the many-worlds interpretation. -/

/-
In a linear order (representing a single timeline), any two events
    are comparable: either a causes b or b causes a.
-/

/-
The past of any event in a branching time structure is totally ordered.
    We model this as: in a tree-like partial order, the downward closure
    of any element is a chain.
-/

/-! ## Causal Diamonds and Light Cones

In special relativity, the causal structure is determined by light cones.
The "causal diamond" between two events p, q is the set of events that
are in the causal future of p and the causal past of q. -/

/-
The causal diamond (intersection of future and past light cones)
    is contained in the "past" cone: if c is in the future of a and
    the past of b, then c is between a and b.
-/

/-! ## Parallel Timelines

In the many-worlds interpretation, timelines that have diverged can
never reconverge. We model this with incomparable elements. -/

/-- Two events are in "parallel timelines" if neither can causally
    influence the other. -/
def parallel_timelines {α : Type*} [PartialOrder α] (a b : α) : Prop :=
  ¬(a ≤ b) ∧ ¬(b ≤ a)

/-
Parallel timelines are symmetric.
-/

/-
In a linear order (single timeline), no two distinct comparable
    events can be in parallel timelines. Actually, no events at all
    can be in parallel timelines in a linear order.
-/

end SciFiMathematics.TemporalLogic


