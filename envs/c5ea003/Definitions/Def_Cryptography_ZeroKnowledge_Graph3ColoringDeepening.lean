-- Prove2me | Definitions.Def_Cryptography_ZeroKnowledge_Graph3ColoringDeepening
-- name    : Cryptography_ZeroKnowledge_Graph3ColoringDeepening
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:30:09.321524+00:00
-- url     : https://prove2.me/theorems/0cc6529f-8898-47c8-b445-8b462bcb2da4
-- title:
--   Aether Catalog definitions — Cryptography_ZeroKnowledge_Graph3ColoringDeepening
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ZeroKnowledge.Graph3ColoringDeepening`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ZeroKnowledge/Graph3ColoringDeepening.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_Graph3Coloring
import Definitions.Def_Cryptography_ZeroKnowledge_Graph3ColoringSimulator

/-!
# Repetition and observational privacy for the graph 3-colouring protocol

This file develops two consequences of the one-round protocol:

* soundness amplification for independent repeated edge challenges; and
* perfect privacy against every deterministic transcript distinguisher.

The probability model for soundness is the exact rational fraction of edges on
which a fixed committed colouring is accepted.  The privacy model uses the PMF
transcript distributions from `Graph3ColoringSimulator`.
-/

namespace ZK.Graph3Coloring

open Finset
open scoped Classical

variable {V : Type*}

/-- The exact one-round acceptance probability for a fixed committed colouring,
when the verifier samples uniformly from the edge set. -/
def acceptanceProbability (E : Finset (V × V)) (c' : V → Fin 3) : ℚ :=
  ((E.filter (fun e => c' e.1 ≠ c' e.2)).card : ℚ) / E.card

/-- The exact one-round rejection probability for a fixed committed colouring. -/
def rejectionProbability (E : Finset (V × V)) (c' : V → Fin 3) : ℚ :=
  ((E.filter (fun e => c' e.1 = c' e.2)).card : ℚ) / E.card





/-- The transcript distribution on a concrete challenged edge of a properly
3-coloured graph. -/
noncomputable def edgeTranscriptDist (E : Finset (V × V)) (c : V → Fin 3)
    (hc : IsProperColoring E c) (e : V × V) (he : e ∈ E) : PMF DistinctPair :=
  realTranscriptDist (c e.1) (c e.2) (hc e he)

/-- A deterministic observer's probability of returning `true` on a transcript. -/
noncomputable def distinguisherAcceptance
    (μ : PMF DistinctPair) (D : DistinctPair → Bool) : ENNReal :=
  ∑' p, if D p then μ p else 0





end ZK.Graph3Coloring


