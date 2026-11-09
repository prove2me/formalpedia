-- Prove2me | Definitions.Def_Couret_STAT_TRANS_11_FirstAdmittedBridge_28633a578269
-- name    : Couret_STAT_TRANS_11_FirstAdmittedBridge_28633a578269
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:03:08.009578+00:00
-- url     : https://prove2.me/theorems/93f92484-4a2a-495c-9e1f-c2e14a370b74
-- title:
--   A recorded G30-to-T16 justification bridge
-- statement:
--   Within StatusTransport.FirstAdmittedBridge, g30ToT16JustificationReceipt is a BridgeReceipt from g30Finite to t16FixedModulus, on the justification axis and with proof dependency kind. Its statement records transport of the A1 rational U(30) inverse identity to the real group algebra in A2 via rationalToReal; its witness string names tau_mul_sigma and tauR_mul_sigmaR and their source files. Its version string pins A1 blob 40072f43ce3ebac6959fd04e86321818567b1c4c and A2 blob f14a47b397de6314e68e0c9e014d15f36eebb799. Only justification is listed among reopened axes. The structure includes proofs of the internal cross-case, nonempty-string, reopened-axis, and policy conditions. productionBridgeReceiptsV1 is the singleton list containing this receipt. The data records the bridge and its references; the bundle does not independently authenticate those artifacts or transport semantic truth, replay, novelty, or publication status.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/8a8227048f12169067627c9a591ee5448bdfc0b9/research/lean/CouretOaiBridge01/STAT_TRANS_11_FirstAdmittedBridge.lean; source file SHA-256 284266f3cbb33cc03c3c72d5c8c992c75377417437390531c742adc4c285c8d8

import Mathlib.Data.Set.Basic
import Definitions.Def_Couret_STAT_TRANS_10_BridgeReceiptMutationSuite_2f6736ccd928

/-!
# STAT-TRANS-11 — First admitted bridge

This layer admits the first real cross-case bridge receipt.

The bridge is deliberately narrow:
G30 finite inverse support -> T16 fixed-modulus proof justification.

It does NOT transport semantic truth, replay status, novelty, publication,
or any global analytic claim.

The witness is already present in Lean:
A2 imports A1 and proves `tauR_mul_sigmaR` by applying `rationalToReal`
to A1's `tau_mul_sigma`.

No RH claim. No novelty claim.
-/

-- Branch-local elaboration workaround for large nested decidable BridgeReceipt.
-- The previous CI build hit maximum recursion depth at fields crossCase and statementNonempty.
-- This option affects elaboration capacity only; it does not add axioms or alter the statements.
set_option maxRecDepth 4096

namespace CouretOaiBridge01
namespace StatusTransport
namespace FirstAdmittedBridge

open ConcreteRegistry
open RefinedPolicy
open BridgeReceipts

/--
First production bridge receipt.

Interpretation:
the justification of the T16 fixed-modulus construction depends on the
finite U(30) inverse certificate from A1.
-/
def g30ToT16JustificationReceipt : BridgeReceipt where
  source := .g30Finite
  target := .t16FixedModulus
  axis := .justification
  kind := .proof
  bridgeStatement :=
    "A2 transports the A1 rational U(30) inverse certificate to the real group algebra; tauR_mul_sigmaR is obtained from tau_mul_sigma via rationalToReal."
  witnessRef :=
    "research/lean/CouretOaiBridge01/BRIDGE01_A2_FixedModulusNoGain.lean: tauR_mul_sigmaR; source theorem BRIDGE01_A1_U30KernelInverse.lean: tau_mul_sigma"
  versionRef :=
    "repo=alexcour/couret-finite-verifications; A1_blob=40072f43ce3ebac6959fd04e86321818567b1c4c; A2_blob=f14a47b397de6314e68e0c9e014d15f36eebb799"
  reopenedAxes := [.justification]
  crossCase := by decide
  statementNonempty := by decide
  witnessNonempty := by decide
  versionNonempty := by decide
  axisReopened := by simp
  policyOk := by rfl

/-- Production bridge registry, version 1. -/
def productionBridgeReceiptsV1 : List BridgeReceipt :=
  [g30ToT16JustificationReceipt]













end FirstAdmittedBridge
end StatusTransport
end CouretOaiBridge01


