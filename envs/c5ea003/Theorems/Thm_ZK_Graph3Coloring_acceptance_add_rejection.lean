-- Prove2me | Theorems.Thm_ZK_Graph3Coloring_acceptance_add_rejection
-- name    : ZK.Graph3Coloring.acceptance_add_rejection
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:08:30.880703+00:00
-- url     : https://prove2.me/theorems/3a51cafa-2d8b-4e45-99c0-98358cc3c975
-- title:
--   Acceptance and rejection partition the edge challenges.
-- statement:
--   Acceptance and rejection partition the edge challenges.
--
--   ```lean
--   theorem ZK.Graph3Coloring.acceptance_add_rejection(E : Finset (V × V)) (c' : V → Fin 3)
--       (hE : 0 < E.card) :
--       acceptanceProbability E c' + rejectionProbability E c' = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/ZeroKnowledge/Graph3ColoringDeepening.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ZeroKnowledge/Graph3ColoringDeepening.lean#L31

-- Thm stub generated from Cryptography/ZeroKnowledge/Graph3ColoringDeepening.lean
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_Graph3ColoringDeepening
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

open ZK.Graph3Coloring

open Finset
open scoped Classical

variable {V : Type*}

theorem ZK.Graph3Coloring.acceptance_add_rejection(E : Finset (V × V)) (c' : V → Fin 3)
    (hE : 0 < E.card) :
    acceptanceProbability E c' + rejectionProbability E c' = 1 := by sorry
