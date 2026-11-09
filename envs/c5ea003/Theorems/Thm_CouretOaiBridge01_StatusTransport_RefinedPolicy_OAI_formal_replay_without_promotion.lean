-- Prove2me | Theorems.Thm_CouretOaiBridge01_StatusTransport_RefinedPolicy_OAI_formal_replay_without_promotion
-- name    : CouretOaiBridge01.StatusTransport.RefinedPolicy.OAI_formal_replay_without_promotion
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:01:36.712751+00:00
-- url     : https://prove2.me/theorems/3b0c7f47-ca56-4843-aa99-ce15cc2dff85
-- title:
--   Oai formal replay without promotion
-- statement:
--   The refined policy permits proof edges for semantic, replay and justification review; replay edges only for replay; novelty edges only for novelty; documentary edges for no axis. For the fixed four-node graph, W_axis^f(X,Y) is the Boolean test for a permitted walk from X to Y of length at most fuel f, including the length-zero walk. Use edges A→B (replay), B→C (documentary), with D isolated. At fuel 3, refined replay A→B is true, justification A→B is false and novelty A→D is false.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_07_RefinedPolicy.lean#L210-L216, lines 210–216; source file SHA-256 614c7160a8c2f4fbe117be5d002aea4a89b078975e4b6fef00171ed27e326e4f; theorem CouretOaiBridge01.StatusTransport.RefinedPolicy.OAI_formal_replay_without_promotion

import Definitions.Def_Couret_STAT_TRANS_07_RefinedPolicy_ed1e12af9529
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



















/-! Fully executable 4 x 4 policy matrix. -/




/-! Mutation suite: support loss, novelty-only, replay-only, documentary,
    multi-hop, disconnected cycle, and four scientific *models*. -/

theorem OAI_formal_replay_without_promotion :
    walkV2 oaiCase .replay 3 .A .B = true ∧
    walkV2 oaiCase .justification 3 .A .B = false ∧
    walkV2 oaiCase .novelty 3 .A .D = false := by sorry


end RefinedPolicy
end StatusTransport
end CouretOaiBridge01
