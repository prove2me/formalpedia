-- Prove2me | Definitions.Def_Couret_STAT_TRANS_13_BridgeRevocation_01cdfed00ec1
-- name    : Couret_STAT_TRANS_13_BridgeRevocation_01cdfed00ec1
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:04:01.18293+00:00
-- url     : https://prove2.me/theorems/6cef1cf9-fb99-4417-918d-c86e3f696fe4
-- title:
--   Enabled receipt edges with retained audit metadata
-- statement:
--   A governed receipt pairs a historical bridge receipt with an enabled Boolean. Two singleton registries contain the same G30-to-T16 justification receipt, once enabled and once disabled. The governed receipt relation admits an edge exactly when some listed receipt is enabled and its axis, source and target match the requested values. The governed bridged relation is the union of these enabled receipt edges with the local refined dependency relation. This construction separates preservation of the receipt object from permission to use its current direct transport edge. It makes no assertion that disabling a receipt falsifies either endpoint claim or erases every possible path in a larger graph.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/f72b0e6ff3408c36460034dc02c539a1fe7e8233/research/lean/CouretOaiBridge01/STAT_TRANS_13_BridgeRevocation.lean; source file SHA-256 65bf158abed25be0c2894ee1660e996bc9623ab11c4ad9856096b8e7a976acc4

import Mathlib.Data.Set.Basic
import Definitions.Def_Couret_STAT_TRANS_12_FirstBridgeInvalidation_20076e79da66

/-!
# STAT-TRANS-13 — Controlled bridge revocation

This layer separates the historical existence of a BridgeReceipt from its
current admission state.

Revoking the first G30 -> T16 justification receipt must remove the cross-case
transport while preserving:
- the receipt metadata for audit;
- the local T16 proof graph;
- all scope firewalls and axis separation.

Revocation means "do not use this receipt for current transport".  It does not
rewrite history and does not assert that either endpoint claim is false.

No RH claim. No novelty claim.
-/

namespace CouretOaiBridge01
namespace StatusTransport
namespace BridgeRevocation

open ConcreteRegistry
open RefinedPolicy
open BridgeReceipts
open FirstAdmittedBridge

/-- A historical receipt together with its current admission bit. -/
structure GovernedReceipt where
  receipt : BridgeReceipt
  enabled : Bool

def enabledFirstBridge : GovernedReceipt :=
  { receipt := g30ToT16JustificationReceipt, enabled := true }

def revokedFirstBridge : GovernedReceipt :=
  { receipt := g30ToT16JustificationReceipt, enabled := false }

/-- Production registry before revocation. -/
def governedRegistryV1 : List GovernedReceipt :=
  [enabledFirstBridge]

/-- Same historical receipt, but disabled for current transport. -/
def governedRegistryV1Revoked : List GovernedReceipt :=
  [revokedFirstBridge]

/-- Only enabled governed receipts contribute an exceptional relation edge. -/
def GovernedReceiptRelation
    (registry : List GovernedReceipt)
    (axis : StatusAxisV2) (a b : ConcreteNode) : Prop :=
  ∃ g ∈ registry,
    g.enabled = true ∧
    g.receipt.axis = axis ∧
    g.receipt.source = a ∧
    g.receipt.target = b

/-- Base local graph plus currently enabled governed receipts. -/
def GovernedBridgedRelation
    (registry : List GovernedReceipt)
    (axis : StatusAxisV2) (a b : ConcreteNode) : Prop :=
  V2Relation concreteEdges axis a b ∨
  GovernedReceiptRelation registry axis a b















end BridgeRevocation
end StatusTransport
end CouretOaiBridge01


