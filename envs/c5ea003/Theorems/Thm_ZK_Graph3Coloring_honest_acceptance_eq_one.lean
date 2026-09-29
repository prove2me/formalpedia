-- Prove2me | Theorems.Thm_ZK_Graph3Coloring_honest_acceptance_eq_one
-- name    : ZK.Graph3Coloring.honest_acceptance_eq_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:08:18.57727+00:00
-- url     : https://prove2.me/theorems/4e1462de-a671-4e9c-921c-883c593500e2
-- title:
--   Perfect completeness as a probability statement.
-- statement:
--   **Perfect completeness as a probability statement.** A proper commitment is
--   accepted on every edge, hence with probability one.
--
--   ```lean
--   theorem ZK.Graph3Coloring.honest_acceptance_eq_one(E : Finset (V × V)) (c : V → Fin 3)
--       (hE : 0 < E.card) (hc : IsProperColoring E c) :
--       acceptanceProbability E c = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/ZeroKnowledge/Graph3ColoringDeepening.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ZeroKnowledge/Graph3ColoringDeepening.lean#L47

-- Thm stub generated from Cryptography/ZeroKnowledge/Graph3ColoringDeepening.lean
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_Graph3Coloring
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

theorem ZK.Graph3Coloring.honest_acceptance_eq_one(E : Finset (V × V)) (c : V → Fin 3)
    (hE : 0 < E.card) (hc : IsProperColoring E c) :
    acceptanceProbability E c = 1 := by sorry
