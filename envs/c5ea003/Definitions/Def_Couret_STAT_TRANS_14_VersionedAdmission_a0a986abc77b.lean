-- Prove2me | Definitions.Def_Couret_STAT_TRANS_14_VersionedAdmission_a0a986abc77b
-- name    : Couret_STAT_TRANS_14_VersionedAdmission_a0a986abc77b
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:04:43.663549+00:00
-- url     : https://prove2.me/theorems/bb3b1e3f-f565-44be-a7aa-072f3f06f2b0
-- title:
--   Pinned witness snapshots and guarded receipt admission
-- statement:
--   Within StatusTransport.VersionedAdmission, expectedA1Blob and expectedA2Blob are the fixed object strings 40072f43ce3ebac6959fd04e86321818567b1c4c and f14a47b397de6314e68e0c9e014d15f36eebb799. WitnessSnapshot records the observed A1/A2 object strings, presence of both artifacts, presence of both declarations, and a localBuildValidated Boolean. pinnedSnapshot sets the expected strings and all five flags to true. snapshotAdmissible is the Boolean conjunction of both exact object-string matches and every presence/validation flag. enabledVersionedReceipt additionally requires that the GovernedReceipt is enabled, its axis/source/target equal the requested values, and permitsV2 approves its dependency kind on that axis. A missing flag, changed object string, mismatched endpoint or axis, disabled receipt, or disallowed dependency kind rejects admission. These definitions consume supplied observations; they do not inspect Git, verify builds, or authenticate external certificates.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/f72b0e6ff3408c36460034dc02c539a1fe7e8233/research/lean/CouretOaiBridge01/STAT_TRANS_14_VersionedAdmission.lean; source file SHA-256 d0ea93469e49656e3d8531cfdac32348c680b5e16273b5c67edf5b332e20b977

import Mathlib.Data.Set.Basic
import Definitions.Def_Couret_STAT_TRANS_13_BridgeRevocation_01cdfed00ec1

/-!
STAT-TRANS-14 — Pinned certificate freshness and fail-closed admission.

This is a VERSIONED policy model, not an external artifact authenticator.
A Boolean attestation must be supplied by a separate verification process.
Changing or withdrawing a witness disables the cross-case receipt, while
preserving the historical record and the local T16 proof edge.

An invalidation means "recheck justification", not "theorem is false".
NO RH CLAIM, NO NOVELTY CLAIM, NO PUBLICATION PROMOTION.
-/

namespace CouretOaiBridge01
namespace StatusTransport
namespace VersionedAdmission

open ConcreteRegistry
open RefinedPolicy
open BridgeReceipts
open FirstAdmittedBridge
open BridgeRevocation

/-- The exact source/target Git object identities from STAT-TRANS-09. -/
def expectedA1Blob : String :=
  "40072f43ce3ebac6959fd04e86321818567b1c4c"

def expectedA2Blob : String :=
  "f14a47b397de6314e68e0c9e014d15f36eebb799"

/-- Model of an observed environment. The booleans are observations,
    NOT mechanically inferred proof certificates. -/
structure WitnessSnapshot where
  a1Blob : String
  a2Blob : String
  a1Present : Bool
  a2Present : Bool
  a1DeclarationPresent : Bool
  a2DeclarationPresent : Bool
  localBuildValidated : Bool
  deriving Repr, DecidableEq

def pinnedSnapshot : WitnessSnapshot where
  a1Blob := expectedA1Blob
  a2Blob := expectedA2Blob
  a1Present := true
  a2Present := true
  a1DeclarationPresent := true
  a2DeclarationPresent := true
  localBuildValidated := true

/-- Any missing, changed or unvalidated component rejects new admission. -/
def snapshotAdmissible (s : WitnessSnapshot) : Bool :=
  (s.a1Blob == expectedA1Blob) &&
  (s.a2Blob == expectedA2Blob) &&
  s.a1Present && s.a2Present &&
  s.a1DeclarationPresent && s.a2DeclarationPresent &&
  s.localBuildValidated

/-- A versioned receipt can only be used on its explicitly declared axis,
    source and target. This test does not claim external trust in the flags. -/
def enabledVersionedReceipt (g : GovernedReceipt)
    (s : WitnessSnapshot) (axis : StatusAxisV2)
    (src dst : ConcreteNode) : Bool :=
  g.enabled && snapshotAdmissible s &&
  decide (g.receipt.axis = axis) &&
  decide (g.receipt.source = src) &&
  decide (g.receipt.target = dst) &&
  permitsV2 axis g.receipt.kind

































end VersionedAdmission
end StatusTransport
end CouretOaiBridge01


