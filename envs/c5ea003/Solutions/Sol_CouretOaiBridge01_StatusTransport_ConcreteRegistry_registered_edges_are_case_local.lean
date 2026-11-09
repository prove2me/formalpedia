-- Prove2me | solution 1 for CouretOaiBridge01.StatusTransport.ConcreteRegistry.registered_edges_are_case_local
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:30:26.551718+00:00
-- url     : https://prove2.me/submissions/4908eb5c-a910-4a68-835c-b29cc62203e5

import Definitions.Def_Couret_STAT_TRANS_07_ConcreteRegistry_d1fd54ec4183
import Mathlib.Data.Set.Basic
import Definitions.Def_Couret_STAT_TRANS_06_AdversarialCases_e73cf4a1e1dc

/-!
# STAT-TRANS-07 — Concrete scientific case registry

This layer replaces the generic A/B/C/D labels by concrete claim identifiers
for the four first scientific case studies.

Artifact ids are metadata only. Lean certifies the graph topology and the
typed propagation policy; it does not authenticate Google Drive or GitHub
contents from a string identifier.

No RH claim. No novelty claim.
-/

namespace CouretOaiBridge01
namespace StatusTransport
namespace ConcreteRegistry













/-- Every registered edge remains inside one scientific case. -/
theorem p2m_local_registered_edges_are_case_local :
    ∀ edge ∈ concreteEdges, caseOf edge.source = caseOf edge.target := by
  intro edge hedge
  simp [concreteEdges, e] at hedge
  rcases hedge with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl













end ConcreteRegistry
end StatusTransport
end CouretOaiBridge01

theorem solution : ∀
  (edge :
    CouretOaiBridge01.StatusTransport.TypedEdge.{0} CouretOaiBridge01.StatusTransport.ConcreteRegistry.ConcreteNode),
  @Membership.mem.{0, 0}
      (CouretOaiBridge01.StatusTransport.TypedEdge.{0} CouretOaiBridge01.StatusTransport.ConcreteRegistry.ConcreteNode)
      (List.{0}
        (CouretOaiBridge01.StatusTransport.TypedEdge.{0}
          CouretOaiBridge01.StatusTransport.ConcreteRegistry.ConcreteNode))
      (@List.instMembership.{0}
        (CouretOaiBridge01.StatusTransport.TypedEdge.{0}
          CouretOaiBridge01.StatusTransport.ConcreteRegistry.ConcreteNode))
      CouretOaiBridge01.StatusTransport.ConcreteRegistry.concreteEdges edge →
    @Eq.{1} CouretOaiBridge01.StatusTransport.ConcreteRegistry.ScientificCase
      (CouretOaiBridge01.StatusTransport.ConcreteRegistry.caseOf
        (@CouretOaiBridge01.StatusTransport.TypedEdge.source.{0}
          CouretOaiBridge01.StatusTransport.ConcreteRegistry.ConcreteNode edge))
      (CouretOaiBridge01.StatusTransport.ConcreteRegistry.caseOf
        (@CouretOaiBridge01.StatusTransport.TypedEdge.target.{0}
          CouretOaiBridge01.StatusTransport.ConcreteRegistry.ConcreteNode edge)) := @_root_.CouretOaiBridge01.StatusTransport.ConcreteRegistry.p2m_local_registered_edges_are_case_local

