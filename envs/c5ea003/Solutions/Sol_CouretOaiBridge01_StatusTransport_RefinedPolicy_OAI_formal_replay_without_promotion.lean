-- Prove2me | solution 1 for CouretOaiBridge01.StatusTransport.RefinedPolicy.OAI_formal_replay_without_promotion
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:01:43.188205+00:00
-- url     : https://prove2.me/submissions/824ae6d3-62f9-4196-9f4d-f3ca007b5ce1

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

























/-- OAI-7/8: comparator replay effect does not automatically promote
    semantic correctness, originality, or publication state. -/
theorem p2m_local_OAI_formal_replay_without_promotion :
    walkV2 oaiCase .replay 3 .A .B = true ∧
    walkV2 oaiCase .justification 3 .A .B = false ∧
    walkV2 oaiCase .novelty 3 .A .D = false := by
  decide

end RefinedPolicy
end StatusTransport
end CouretOaiBridge01

theorem solution : And
  (@Eq.{1} Bool
    (CouretOaiBridge01.StatusTransport.RefinedPolicy.walkV2 CouretOaiBridge01.StatusTransport.AdversarialCases.oaiCase
      CouretOaiBridge01.StatusTransport.RefinedPolicy.StatusAxisV2.replay
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      CouretOaiBridge01.StatusTransport.MutationSuite.Node.A CouretOaiBridge01.StatusTransport.MutationSuite.Node.B)
    Bool.true)
  (And
    (@Eq.{1} Bool
      (CouretOaiBridge01.StatusTransport.RefinedPolicy.walkV2 CouretOaiBridge01.StatusTransport.AdversarialCases.oaiCase
        CouretOaiBridge01.StatusTransport.RefinedPolicy.StatusAxisV2.justification
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        CouretOaiBridge01.StatusTransport.MutationSuite.Node.A CouretOaiBridge01.StatusTransport.MutationSuite.Node.B)
      Bool.false)
    (@Eq.{1} Bool
      (CouretOaiBridge01.StatusTransport.RefinedPolicy.walkV2 CouretOaiBridge01.StatusTransport.AdversarialCases.oaiCase
        CouretOaiBridge01.StatusTransport.RefinedPolicy.StatusAxisV2.novelty
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        CouretOaiBridge01.StatusTransport.MutationSuite.Node.A CouretOaiBridge01.StatusTransport.MutationSuite.Node.D)
      Bool.false)) := @_root_.CouretOaiBridge01.StatusTransport.RefinedPolicy.p2m_local_OAI_formal_replay_without_promotion

