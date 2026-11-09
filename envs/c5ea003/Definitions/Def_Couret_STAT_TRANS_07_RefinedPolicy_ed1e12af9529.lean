-- Prove2me | Definitions.Def_Couret_STAT_TRANS_07_RefinedPolicy_ed1e12af9529
-- name    : Couret_STAT_TRANS_07_RefinedPolicy_ed1e12af9529
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:41.50004+00:00
-- url     : https://prove2.me/theorems/898f1ef9-3aff-4c22-af6e-088182c95a35
-- title:
--   Versioned assurance propagation and bounded synthetic walks
-- statement:
--   In StatusTransport.RefinedPolicy, StatusAxisV2 has semantic, replay, novelty, and justification. permitsV2 allows exactly semantic/proof, replay/proof, replay/replay, novelty/novelty, and justification/proof; all other axis/kind combinations are false. MutationV2 α records a node, a Delta, and proofSupportChanged, default false. touches uses the earlier semantic, replay, or novelty invalidator on those axes; justification is touched by a semantic change, epistemic change, or proof-support change. V2Seed holds at a listed changed node with touches=true. V2Relation follows a listed edge only when its kind is permitted on the axis. V2Impacted applies the imported impact closure to that seed and relation. walkV2 is a Boolean walk search on the four-node MutationSuite type: at fuel zero it tests equality; at successor fuel it tests equality or a permitted outgoing edge followed by a recursive search. Thus fuel limits path length and equal endpoints pass even with zero fuel. explicitBibliography is the two-edge novelty list A→B→D. The bounded search is not a general non-reachability certificate for arbitrary graphs; an impact means recheck the relevant assurance.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_07_RefinedPolicy.lean; source file SHA-256 614c7160a8c2f4fbe117be5d002aea4a89b078975e4b6fef00171ed27e326e4f

import Mathlib.Data.Set.Basic
import Definitions.Def_Couret_STAT_TRANS_06_AdversarialCases_e73cf4a1e1dc

/-!
# STAT-TRANS-07 — Justification, refined dependency policy and adversarial mutations

Versioned policy: the original `permits` in STAT-TRANS-04 is retained as
a reproducible conservative baseline. This policy makes proof-support status
independent of proposition semantics, replay, novelty and publication.

An impact means "recheck this assurance", never "the statement is false".
No RH claim, no novelty or publication certification.
-/

namespace CouretOaiBridge01
namespace StatusTransport
namespace RefinedPolicy

open MutationSuite
open AdversarialCases

/-- Four distinct forms of assurance, with diffusion/publication kept outside
    the proof/replay/novelty impact graph. -/
inductive StatusAxisV2 where
  | semantic
  | replay
  | novelty
  | justification
  deriving Repr, DecidableEq

/-- Versioned refinement. Proof edges do not *automatically* transport
    novelty: a bibliographic relationship requires an explicit novelty edge.
    The original conservative policy remains available for comparison. -/
def permitsV2 : StatusAxisV2 → DependencyKind → Bool
  | .semantic, .proof => true
  | .replay, .proof => true
  | .replay, .replay => true
  | .novelty, .novelty => true
  | .justification, .proof => true
  | _, _ => false

/-- Extra observation required to distinguish a changed proof dependency
    from a changed executable dependency. Never infer this from an arbitrary
    dependency hash. -/
structure MutationV2 (α : Type*) where
  node : α
  delta : Delta
  proofSupportChanged : Bool := false

/-- Local revocation of a justification can occur without changing the
    proposition, and independently of reproducibility. -/
def touches (axis : StatusAxisV2) (δ : Delta)
    (proofSupportChanged : Bool) : Bool :=
  match axis with
  | .semantic => δ.invalidatesSemantic
  | .replay => δ.invalidatesReplay
  | .novelty => δ.invalidatesNovelty
  | .justification =>
      δ.semanticChanged || δ.epistemicChanged || proofSupportChanged

def V2Seed {α : Type*} (axis : StatusAxisV2)
    (changes : List (MutationV2 α)) (x : α) : Prop :=
  ∃ c ∈ changes, c.node = x ∧
    touches axis c.delta c.proofSupportChanged = true

def V2Relation {α : Type*} (es : List (TypedEdge α))
    (axis : StatusAxisV2) (a b : α) : Prop :=
  ∃ e ∈ es, e.source = a ∧ e.target = b ∧
    permitsV2 axis e.kind = true

def V2Impacted {α : Type*} (es : List (TypedEdge α))
    (axis : StatusAxisV2) (changes : List (MutationV2 α))
    (x : α) : Prop :=
  Impacted (V2Relation es axis) (V2Seed axis changes) x





/-! Fully executable 4 x 4 policy matrix. -/


/-- Executable bounded oracle on four-node synthetic graphs. It cannot be
    used as a general proof of non-reachability on arbitrary graphs. -/
def walkV2 (es : List (TypedEdge Node)) (axis : StatusAxisV2)
    (fuel : Nat) (src dst : Node) : Bool :=
  match fuel with
  | 0 => decide (src = dst)
  | n + 1 =>
      decide (src = dst) ||
        es.any (fun e =>
          decide (e.source = src) &&
          permitsV2 axis e.kind &&
          walkV2 es axis n e.target dst)

/-! Mutation suite: support loss, novelty-only, replay-only, documentary,
    multi-hop, disconnected cycle, and four scientific *models*. -/













def explicitBibliography : List (TypedEdge Node) :=
  [{ source := .A, target := .B, kind := .novelty },
   { source := .B, target := .D, kind := .novelty }]













end RefinedPolicy
end StatusTransport
end CouretOaiBridge01


