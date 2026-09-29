-- Prove2me | solution 1 for ZK.Graph3Coloring.honest_acceptance_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:39:18.918914+00:00
-- url     : https://prove2.me/submissions/fe5e8130-eb4d-46a2-92c8-f346b40caa50

-- Sol generated from Cryptography/ZeroKnowledge/Graph3ColoringDeepening.lean
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














open ZK.Graph3Coloring in
theorem solution(E : Finset (V × V)) (c : V → Fin 3)
    (hE : 0 < E.card) (hc : IsProperColoring E c) :
    acceptanceProbability E c = 1 := by
  unfold acceptanceProbability
  have hall : E.filter (fun e => c e.1 ≠ c e.2) = E := by
    ext e
    simp only [mem_filter]
    constructor
    · exact fun h => h.1
    · intro he
      exact ⟨he, hc e he⟩
  rw [hall]
  have hne : (E.card : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hE)
  exact div_self hne
