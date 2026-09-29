-- Prove2me | solution 1 for ZK.Graph3Coloring.acceptance_add_rejection
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:39:18.426853+00:00
-- url     : https://prove2.me/submissions/7886c3d4-f28b-458a-a3a4-9431870e4dd0

-- Sol generated from Cryptography/ZeroKnowledge/Graph3ColoringDeepening.lean
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














open ZK.Graph3Coloring in
theorem solution(E : Finset (V × V)) (c' : V → Fin 3)
    (hE : 0 < E.card) :
    acceptanceProbability E c' + rejectionProbability E c' = 1 := by
  unfold acceptanceProbability rejectionProbability
  have hcard := Finset.card_filter_add_card_filter_not
    (s := E) (fun e => c' e.1 ≠ c' e.2)
  simp only [not_ne_iff] at hcard
  have hcardQ :
      ((E.filter (fun e => c' e.1 ≠ c' e.2)).card : ℚ) +
        (E.filter (fun e => c' e.1 = c' e.2)).card = E.card := by
    exact_mod_cast hcard
  have hne : (E.card : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hE)
  field_simp
  exact hcardQ
