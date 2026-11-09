-- Prove2me | Theorems.Thm_CouretOaiBridge01_StatusTransport_ConcreteRegistry_no_cross_case_paths
-- name    : CouretOaiBridge01.StatusTransport.ConcreteRegistry.no_cross_case_paths
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:01:19.904166+00:00
-- url     : https://prove2.me/theorems/45659c38-0990-4d4a-8d6e-74bc8cc4d3e4
-- title:
--   Four specified cross-case bounded walks are absent
-- statement:
--   Consider the source registry of sixteen nodes partitioned into four cases: G30, T16, Cayley and OAI seven-eighths. A Boolean walk query W(axis,fuel,source,target) starts with equality at fuel zero and otherwise allows equality or one permitted registered edge followed by a query with one less fuel. At fuel eight, all four queries below are false: semantic G30 finite to T16 derived no-gain; replay T16 abstract to OAI replay; novelty Cayley prior art to OAI novelty audit; semantic OAI verifier to G30 unsupported global extension.
--
--   $$W(\mathrm{axis},8,\mathrm{source},\mathrm{target})=\mathrm{false}\quad\text{for each of these four specified triples}.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_07_ConcreteRegistry.lean#L149-L155, lines 149–155; source file SHA-256 f05696e1b6dceb29b803de0750e8abb77295768df7abf264c8b4fef8d5008900; theorem CouretOaiBridge01.StatusTransport.ConcreteRegistry.no_cross_case_paths

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

theorem no_cross_case_paths :
    walkConcrete .semantic 8 .g30Finite .t16DerivedNoGain = false ∧
    walkConcrete .replay 8 .t16Abstract .oaiReplay = false ∧
    walkConcrete .novelty 8 .cayleyPriorArt .oaiNoveltyAudit = false ∧
    walkConcrete .semantic 8 .oaiVerifier .g30GlobalUnsupported = false := by sorry


end ConcreteRegistry
end StatusTransport
end CouretOaiBridge01
