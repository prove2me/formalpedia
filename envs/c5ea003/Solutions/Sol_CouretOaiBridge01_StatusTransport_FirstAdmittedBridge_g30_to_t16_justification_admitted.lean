-- Prove2me | solution 1 for CouretOaiBridge01.StatusTransport.FirstAdmittedBridge.g30_to_t16_justification_admitted
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:01:56.017497+00:00
-- url     : https://prove2.me/submissions/30de50be-3c87-4ff8-b69e-7dd492d68a6a

import Definitions.Def_Couret_STAT_TRANS_11_FirstAdmittedBridge_28633a578269
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





/-- The first bridge is admitted on justification. -/
theorem p2m_local_g30_to_t16_justification_admitted :
    ReceiptRelation productionBridgeReceiptsV1
      .justification .g30Finite .t16FixedModulus := by
  exact ⟨g30ToT16JustificationReceipt, by simp [productionBridgeReceiptsV1],
    rfl, rfl, rfl⟩











end FirstAdmittedBridge
end StatusTransport
end CouretOaiBridge01

theorem solution : CouretOaiBridge01.StatusTransport.BridgeReceipts.ReceiptRelation
  CouretOaiBridge01.StatusTransport.FirstAdmittedBridge.productionBridgeReceiptsV1
  CouretOaiBridge01.StatusTransport.RefinedPolicy.StatusAxisV2.justification
  CouretOaiBridge01.StatusTransport.ConcreteRegistry.ConcreteNode.g30Finite
  CouretOaiBridge01.StatusTransport.ConcreteRegistry.ConcreteNode.t16FixedModulus := @_root_.CouretOaiBridge01.StatusTransport.FirstAdmittedBridge.p2m_local_g30_to_t16_justification_admitted

