-- Prove2me | Definitions.Def_Couret_STAT_TRANS_04_TypedDependencies_3df632007942
-- name    : Couret_STAT_TRANS_04_TypedDependencies_3df632007942
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:15.207318+00:00
-- url     : https://prove2.me/theorems/1d70c501-58a1-4a9b-a39c-7c5a9a10912b
-- title:
--   Axis-specific typed dependency relations
-- statement:
--   A typed edge records source, target and one of four kinds: proof, replay, novelty or documentary. The baseline policy has three impact axes. Proof edges carry semantic, replay and novelty reconsideration; replay edges carry replay only; novelty edges carry novelty only; documentary edges carry none. For a finite edge list, the relation on an axis contains exactly listed edges permitted on that axis. The corresponding seed predicate selects local changes relevant to that axis, and typed impact uses the imported reachability-based impact construction. These are formal review-propagation definitions; they do not equate impact with falsity or collapse the axes into one scalar status. This is the baseline policy, distinct from the separately versioned refined policy.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_04_TypedDependencies.lean; source file SHA-256 281beb127656947f4f40697a7241993ba3e4cf18764a18bef5cb9ba1952cd375

import Mathlib.Data.Set.Basic
import Definitions.Def_Couret_STAT_TRANS_03_DependencyGraph_a12904c0d89d

/-!
# STAT-TRANS-04 — Typed dependencies

This layer distinguishes dependency kinds so that invalidation propagates
only along edges relevant to the affected axis.

No global scalar status is introduced.
No RH claim. No novelty claim.
-/

namespace CouretOaiBridge01
namespace StatusTransport

/-- A small first vocabulary of dependency kinds. -/
inductive DependencyKind where
  | proof
  | replay
  | novelty
  | documentary
  deriving Repr, DecidableEq

/-- The invalidation dimension being propagated. -/
inductive ImpactAxis where
  | semantic
  | replay
  | novelty
  deriving Repr, DecidableEq

/-- A typed dependency edge: target directly depends on source. -/
structure TypedEdge (α : Type*) where
  source : α
  target : α
  kind : DependencyKind

/--
Policy saying whether a dependency kind propagates a given invalidation axis.

First conservative policy:
* proof dependencies propagate semantic, replay, and novelty reconsideration;
* replay dependencies propagate replay only;
* novelty dependencies propagate novelty only;
* documentary dependencies propagate none of these three axes.
-/
def permits : ImpactAxis → DependencyKind → Bool
  | .semantic, .proof => true
  | .semantic, _ => false
  | .replay, .proof => true
  | .replay, .replay => true
  | .replay, _ => false
  | .novelty, .proof => true
  | .novelty, .novelty => true
  | .novelty, _ => false

/-- Relation induced by the typed edge list for one impact axis. -/
def TypedRelation {α : Type*}
    (edges : List (TypedEdge α)) (axis : ImpactAxis) (a b : α) : Prop :=
  ∃ e ∈ edges,
    e.source = a ∧
    e.target = b ∧
    permits axis e.kind = true

/-- Select the appropriate local seed predicate for one axis. -/
def SeedFor {α : Type*}
    (axis : ImpactAxis) (changes : List (ChangeAt α)) (x : α) : Prop :=
  match axis with
  | .semantic => SemanticSeed changes x
  | .replay => ReplaySeed changes x
  | .novelty => NoveltySeed changes x

/-- Typed graph impact for one axis. -/
def TypedImpacted {α : Type*}
    (edges : List (TypedEdge α))
    (axis : ImpactAxis)
    (changes : List (ChangeAt α))
    (x : α) : Prop :=
  Impacted (TypedRelation edges axis) (SeedFor axis changes) x



















end StatusTransport
end CouretOaiBridge01


