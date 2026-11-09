-- Prove2me | Definitions.Def_Couret_STAT_TRANS_07_ConcreteRegistry_d1fd54ec4183
-- name    : Couret_STAT_TRANS_07_ConcreteRegistry_d1fd54ec4183
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:22.683419+00:00
-- url     : https://prove2.me/theorems/c7581259-b561-4482-8a1a-d0189a4ef897
-- title:
--   A finite registry of labelled scientific case nodes
-- statement:
--   The registry defines four case labels and sixteen node labels, four for each of G30, T16, Cayley and OAI-7/8. A case map partitions nodes, and a string-valued artifact reference attaches documentary identifiers. Ten fixed typed edges record proof, replay, novelty and documentary dependencies within their respective cases. The executable walk follows only edges admitted by the baseline axis policy for at most its natural fuel, and accepts a zero-length walk from a node to itself even at fuel zero. The strings are metadata, not authentication of remote contents. The definitions formalize a labelled finite graph, not certification of the scientific assertions suggested by its node names.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_07_ConcreteRegistry.lean; source file SHA-256 f05696e1b6dceb29b803de0750e8abb77295768df7abf264c8b4fef8d5008900

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

inductive ScientificCase where
  | g30
  | t16
  | cayley
  | oaiSevenEighths
  deriving Repr, DecidableEq

inductive ConcreteNode where
  | g30Finite
  | g30Local
  | g30GlobalUnsupported
  | g30Documentary
  | t16Abstract
  | t16FixedModulus
  | t16DerivedNoGain
  | t16NoveltyAudit
  | cayleyPriorArt
  | cayleyNoveltyReview
  | cayleyPublicReview
  | cayleyIndependentProof
  | oaiVerifier
  | oaiReplay
  | oaiPublishedNarrative
  | oaiNoveltyAudit
  deriving Repr, DecidableEq

def caseOf : ConcreteNode → ScientificCase
  | .g30Finite
  | .g30Local
  | .g30GlobalUnsupported
  | .g30Documentary => .g30
  | .t16Abstract
  | .t16FixedModulus
  | .t16DerivedNoGain
  | .t16NoveltyAudit => .t16
  | .cayleyPriorArt
  | .cayleyNoveltyReview
  | .cayleyPublicReview
  | .cayleyIndependentProof => .cayley
  | .oaiVerifier
  | .oaiReplay
  | .oaiPublishedNarrative
  | .oaiNoveltyAudit => .oaiSevenEighths

/-- Documentary artifact identifiers. These strings are not authentication proofs. -/
def artifactRef : ConcreteNode → String
  | .g30Finite => "Drive:1BfnMwX8BJYrtGJGx_JY-iT5YfuFYyAwT7MHvKKll27g"
  | .g30Local => "Drive:MOD30-current/local-derived"
  | .g30GlobalUnsupported => "UNSUPPORTED-GLOBAL-EXTENSION"
  | .g30Documentary => "DOCUMENTARY-POINTER"
  | .t16Abstract => "GitHub:research/COURET_OAI_BRIDGE_01_T16.md"
  | .t16FixedModulus => "Lean:BRIDGE01_A2_FixedModulusNoGain"
  | .t16DerivedNoGain => "Claim:T16-fixed-modulus-no-gain"
  | .t16NoveltyAudit => "Novelty:T16-open"
  | .cayleyPriorArt => "GitHub:cayley-prime-translation-cospectrality/PRIOR_ART.md"
  | .cayleyNoveltyReview => "GitHub:cayley-prime-translation-cospectrality/PUBLICATION_STATUS.md"
  | .cayleyPublicReview => "Publication:PUBLIC-REVIEW-0.1.x"
  | .cayleyIndependentProof => "Review:INDEPENDENT-PROOF-OPEN"
  | .oaiVerifier => "openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a"
  | .oaiReplay => "Audit:OAI-7/8-AUDIT-01R"
  | .oaiPublishedNarrative => "OpenAI:quasi-RH-publication"
  | .oaiNoveltyAudit => "Novelty:OAI-7/8-open"

def e (source target : ConcreteNode) (kind : DependencyKind) : TypedEdge ConcreteNode :=
  { source := source, target := target, kind := kind }

def concreteEdges : List (TypedEdge ConcreteNode) :=
  [
    e .g30Finite .g30Local .proof,
    e .g30Local .g30GlobalUnsupported .documentary,
    e .g30GlobalUnsupported .g30Documentary .documentary,

    e .t16Abstract .t16FixedModulus .proof,
    e .t16FixedModulus .t16DerivedNoGain .proof,
    e .t16DerivedNoGain .t16NoveltyAudit .novelty,

    e .cayleyPriorArt .cayleyNoveltyReview .novelty,
    e .cayleyNoveltyReview .cayleyPublicReview .documentary,

    e .oaiVerifier .oaiReplay .replay,
    e .oaiReplay .oaiPublishedNarrative .documentary
  ]



/-- Bounded executable path oracle for the concrete registry. -/
def walkConcrete (axis : ImpactAxis) (fuel : Nat)
    (src dst : ConcreteNode) : Bool :=
  match fuel with
  | 0 => decide (src = dst)
  | n + 1 =>
      decide (src = dst) ||
        concreteEdges.any (fun edge =>
          decide (edge.source = src) &&
          permits axis edge.kind &&
          walkConcrete axis n edge.target dst)











end ConcreteRegistry
end StatusTransport
end CouretOaiBridge01


