-- Prove2me | Definitions.Def_Couret_STAT_TRANS_08_BridgeReceipts_087a93e69025
-- name    : Couret_STAT_TRANS_08_BridgeReceipts_087a93e69025
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:02:12.856537+00:00
-- url     : https://prove2.me/theorems/ae8c56a6-8ad8-4ec2-a45d-173f2a82face
-- title:
--   Typed cross-case transport receipts
-- statement:
--   A BridgeReceipt records concrete source and target nodes in different cases, a status axis and dependency kind, bridge-statement, witness-reference and version-reference strings, and a list of reopened axes. Its proof fields require nonempty strings, membership of the chosen axis in the reopened list and permission by the refined Boolean policy. ReceiptRelation includes exactly source/target/axis triples represented by a receipt in the supplied list; BridgedRelation is the union of that relation with the base registry relation. currentBridgeReceipts is the empty list. Nonempty reference strings are schema constraints and do not authenticate external artifacts.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_08_BridgeReceipts.lean; source file SHA-256 a2817030ed438a98e6bcab5eb9b3ab12126da52b32e8fe7707b8fcf1cc99482e

import Mathlib.Data.Set.Basic
import Definitions.Def_Couret_STAT_TRANS_07_ConcreteRegistry_d1fd54ec4183
import Definitions.Def_Couret_STAT_TRANS_07_RefinedPolicy_ed1e12af9529

/-!
# STAT-TRANS-08 — Bridge receipts

Cross-case transport is forbidden by default.  An exceptional bridge is
represented by an explicit receipt carrying source, target, axis, dependency
kind, bridge statement, witness reference, version reference, and declared
invalidation consequences.

Lean verifies the receipt schema and the graph admission rule.  A string
reference to an external artifact is metadata, not authentication of that
artifact.

No RH claim. No novelty claim.
-/

namespace CouretOaiBridge01
namespace StatusTransport
namespace BridgeReceipts

open ConcreteRegistry
open RefinedPolicy

/-- A typed receipt authorizing one cross-case transport axis. -/
structure BridgeReceipt where
  source : ConcreteNode
  target : ConcreteNode
  axis : StatusAxisV2
  kind : DependencyKind
  bridgeStatement : String
  witnessRef : String
  versionRef : String
  reopenedAxes : List StatusAxisV2
  crossCase : caseOf source ≠ caseOf target
  statementNonempty : bridgeStatement ≠ ""
  witnessNonempty : witnessRef ≠ ""
  versionNonempty : versionRef ≠ ""
  axisReopened : axis ∈ reopenedAxes
  policyOk : permitsV2 axis kind = true

/-- The relation contributed by explicit bridge receipts only. -/
def ReceiptRelation (receipts : List BridgeReceipt)
    (axis : StatusAxisV2) (a b : ConcreteNode) : Prop :=
  ∃ r ∈ receipts, r.axis = axis ∧ r.source = a ∧ r.target = b

/-- Base case-local relation plus exceptional cross-case receipts. -/
def BridgedRelation (receipts : List BridgeReceipt)
    (axis : StatusAxisV2) (a b : ConcreteNode) : Prop :=
  V2Relation concreteEdges axis a b ∨ ReceiptRelation receipts axis a b













/-- No exceptional cross-case bridges are currently admitted. -/
def currentBridgeReceipts : List BridgeReceipt := []







end BridgeReceipts
end StatusTransport
end CouretOaiBridge01


