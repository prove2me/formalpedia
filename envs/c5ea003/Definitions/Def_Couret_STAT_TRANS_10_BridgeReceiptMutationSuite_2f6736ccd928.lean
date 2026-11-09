-- Prove2me | Definitions.Def_Couret_STAT_TRANS_10_BridgeReceiptMutationSuite_2f6736ccd928
-- name    : Couret_STAT_TRANS_10_BridgeReceiptMutationSuite_2f6736ccd928
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:02:37.685244+00:00
-- url     : https://prove2.me/theorems/3a24b554-21f2-4df1-941e-04ea45b0e11b
-- title:
--   Structural bridge-draft validation and synthetic receipts
-- statement:
--   A bridge draft records source and target registry nodes, a refined assurance axis, a dependency kind, statement/witness/version strings and a list of reopened axes. Its Boolean precheck requires distinct scientific cases, three nonempty strings, inclusion of the chosen axis in that list and permission of the edge kind on that axis. Fixed synthetic drafts vary these fields to test acceptance and rejection for semantic, replay, novelty and justification channels. A synthetic semantic receipt carries proofs of its stated structural constraints; this bundle does not insert it into the current registry. Passing the draft precheck does not by itself authenticate the referenced witness, establish the proposition named by a string, or constitute scientific admission.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_10_BridgeReceiptMutationSuite.lean; source file SHA-256 577a41a0270bef14eb9b020e54ed3421c0cf6bb66d2fe6526f3706c1b87392ba

import Mathlib.Data.Set.Basic
import Definitions.Def_Couret_STAT_TRANS_08_BridgeReceipts_087a93e69025

/-!
# STAT-TRANS-10 — Bridge receipt mutation suite

This layer pre-specifies structural ACCEPT / REJECT tests for bridge drafts
before any real cross-case bridge is admitted to `currentBridgeReceipts`.

A structurally accepted draft is not a scientifically admitted bridge.
Admission still requires construction of a `BridgeReceipt` and explicit
registration.

No RH claim. No novelty claim.
-/

namespace CouretOaiBridge01
namespace StatusTransport
namespace BridgeReceiptMutationSuite

open ConcreteRegistry
open RefinedPolicy
open BridgeReceipts

/-- Untrusted bridge proposal before proof-carrying admission. -/
structure BridgeDraft where
  source : ConcreteNode
  target : ConcreteNode
  axis : StatusAxisV2
  kind : DependencyKind
  bridgeStatement : String
  witnessRef : String
  versionRef : String
  reopenedAxes : List StatusAxisV2
  deriving Repr, DecidableEq

/-- Executable structural pre-check. It is necessary, not sufficient, for admission. -/
def draftAccepts (d : BridgeDraft) : Bool :=
  decide (caseOf d.source ≠ caseOf d.target) &&
  decide (d.bridgeStatement ≠ "") &&
  decide (d.witnessRef ≠ "") &&
  decide (d.versionRef ≠ "") &&
  decide (d.axis ∈ d.reopenedAxes) &&
  permitsV2 d.axis d.kind

def validSemanticProof : BridgeDraft :=
  {
    source := .g30Local
    target := .t16Abstract
    axis := .semantic
    kind := .proof
    bridgeStatement := "SYNTHETIC semantic bridge for validator test only"
    witnessRef := "SYNTHETIC-WITNESS"
    versionRef := "SYNTHETIC-V1"
    reopenedAxes := [.semantic]
  }

def sameCaseDraft : BridgeDraft :=
  { validSemanticProof with target := .g30Finite }

def emptyStatementDraft : BridgeDraft :=
  { validSemanticProof with bridgeStatement := "" }

def emptyWitnessDraft : BridgeDraft :=
  { validSemanticProof with witnessRef := "" }

def emptyVersionDraft : BridgeDraft :=
  { validSemanticProof with versionRef := "" }

def axisNotReopenedDraft : BridgeDraft :=
  { validSemanticProof with reopenedAxes := [] }

def documentarySemanticDraft : BridgeDraft :=
  { validSemanticProof with kind := .documentary }

def proofNoveltyDraft : BridgeDraft :=
  { validSemanticProof with axis := .novelty, reopenedAxes := [.novelty] }

def validReplayDraft : BridgeDraft :=
  {
    source := .oaiVerifier
    target := .cayleyPublicReview
    axis := .replay
    kind := .replay
    bridgeStatement := "SYNTHETIC replay bridge for validator test only"
    witnessRef := "SYNTHETIC-REPLAY"
    versionRef := "SYNTHETIC-V1"
    reopenedAxes := [.replay]
  }

def replayAsSemanticDraft : BridgeDraft :=
  { validReplayDraft with axis := .semantic, reopenedAxes := [.semantic] }

def validNoveltyDraft : BridgeDraft :=
  {
    source := .cayleyPriorArt
    target := .t16NoveltyAudit
    axis := .novelty
    kind := .novelty
    bridgeStatement := "SYNTHETIC novelty bridge for validator test only"
    witnessRef := "SYNTHETIC-BIBLIOGRAPHY"
    versionRef := "SYNTHETIC-V1"
    reopenedAxes := [.novelty]
  }

def validJustificationProof : BridgeDraft :=
  {
    source := .t16DerivedNoGain
    target := .oaiVerifier
    axis := .justification
    kind := .proof
    bridgeStatement := "SYNTHETIC justification bridge for validator test only"
    witnessRef := "SYNTHETIC-PROOF-SUPPORT"
    versionRef := "SYNTHETIC-V1"
    reopenedAxes := [.justification]
  }

/-! ## Pre-specified ACCEPT / REJECT matrix -/

























/-!
A concrete synthetic receipt demonstrates the distinction between
"structurally admissible" and "currently registered".  It is never inserted
into `currentBridgeReceipts`.
-/

def syntheticSemanticReceipt : BridgeReceipt where
  source := .g30Local
  target := .t16Abstract
  axis := .semantic
  kind := .proof
  bridgeStatement := "SYNTHETIC semantic bridge for receipt mechanics only"
  witnessRef := "SYNTHETIC-WITNESS"
  versionRef := "SYNTHETIC-V1"
  reopenedAxes := [.semantic]
  crossCase := by decide
  statementNonempty := by decide
  witnessNonempty := by decide
  versionNonempty := by decide
  axisReopened := by simp
  policyOk := by rfl









end BridgeReceiptMutationSuite
end StatusTransport
end CouretOaiBridge01


