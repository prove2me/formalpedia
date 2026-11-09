-- Prove2me | Definitions.Def_Couret_STAT_TRANS_12_FirstBridgeInvalidation_20076e79da66
-- name    : Couret_STAT_TRANS_12_FirstBridgeInvalidation_20076e79da66
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:03:44.308715+00:00
-- url     : https://prove2.me/theorems/ab117aef-5ef9-4fe6-b0fe-0b9a0f9c0b9c
-- title:
--   Production bridge impact and bounded graph traversal
-- statement:
--   Defines a singleton mutation at the G30 finite node with empty default delta and proofSupportChanged=true. ProductionImpacted propagates refined-policy seeds using the base relation augmented by productionBridgeReceiptsV1. productionStepV1 is a Boolean direct-step test over permitted concrete edges plus the justification-only edge from G30 finite to T16 fixed modulus. walkProductionV1 uses natural fuel and the explicit list of sixteen concrete nodes to search such steps, always accepting equal endpoints even at zero fuel. These definitions distinguish the relational impact predicate from a bounded executable walk.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/f72b0e6ff3408c36460034dc02c539a1fe7e8233/research/lean/CouretOaiBridge01/STAT_TRANS_12_FirstBridgeInvalidation.lean; source file SHA-256 700bbed8c4340ce17b17c6da88859ef43abf40a0fe9ce89c1cb1ac77b02c16cd

import Mathlib.Data.Set.Basic
import Definitions.Def_Couret_STAT_TRANS_11_FirstAdmittedBridge_28633a578269

/-!
# STAT-TRANS-12 — Invalidation through the first admitted bridge

This layer tests the operational consequence of the first real receipt.

A proof-support change at G30 finite support must reopen T16 justification
through the admitted receipt, then continue through local T16 proof edges.
It must not create semantic, replay, novelty, or global-G30 impact.

No RH claim. No novelty claim.
-/

namespace CouretOaiBridge01
namespace StatusTransport
namespace FirstBridgeInvalidation

open ConcreteRegistry
open RefinedPolicy
open BridgeReceipts
open FirstAdmittedBridge

def g30ProofSupportLoss : List (MutationV2 ConcreteNode) :=
  [{
    node := .g30Finite
    delta := {}
    proofSupportChanged := true
  }]

def ProductionImpacted
    (axis : StatusAxisV2)
    (changes : List (MutationV2 ConcreteNode))
    (x : ConcreteNode) : Prop :=
  Impacted
    (BridgedRelation productionBridgeReceiptsV1 axis)
    (V2Seed axis changes)
    x























/-- Boolean direct-step oracle matching the production registry V1. -/
def productionStepV1
    (axis : StatusAxisV2) (a b : ConcreteNode) : Bool :=
  concreteEdges.any (fun edge =>
      decide (edge.source = a) &&
      decide (edge.target = b) &&
      permitsV2 axis edge.kind) ||
    (decide (axis = .justification) &&
      decide (a = .g30Finite) &&
      decide (b = .t16FixedModulus))

/-- Bounded executable reachability oracle for the finite production graph. -/
def walkProductionV1
    (axis : StatusAxisV2) (fuel : Nat)
    (src dst : ConcreteNode) : Bool :=
  match fuel with
  | 0 => decide (src = dst)
  | n + 1 =>
      decide (src = dst) ||
      ([.g30Finite, .g30Local, .g30GlobalUnsupported, .g30Documentary,
        .t16Abstract, .t16FixedModulus, .t16DerivedNoGain, .t16NoveltyAudit,
        .cayleyPriorArt, .cayleyNoveltyReview, .cayleyPublicReview,
        .cayleyIndependentProof, .oaiVerifier, .oaiReplay,
        .oaiPublishedNarrative, .oaiNoveltyAudit] : List ConcreteNode).any
        (fun mid =>
          productionStepV1 axis src mid &&
          walkProductionV1 axis n mid dst)



end FirstBridgeInvalidation
end StatusTransport
end CouretOaiBridge01


