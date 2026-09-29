-- Prove2me | solution 1 for mme_stothers_phi233_cyclic_edge_cardinalities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:37:44.229937+00:00
-- url     : https://prove2.me/submissions/3de17467-aea4-4bfa-b590-620b88d3fad7

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_ambient_data

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (N alpha beta gamma delta : ℕ) :
    Nat.card
        (MME.StothersFourth.Phi233.CyclicExactEdge
          N alpha beta gamma delta) =
        (Nat.card
          (MME.StothersFourth.Phi233.ExactProfileAddress
            N alpha beta gamma delta)) ^ 3 ∧
      Nat.card
        (MME.StothersFourth.Phi233.CyclicAmbientEdge
          N alpha beta gamma delta) =
        (Nat.card
          (MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta)) ^ 3 := by
  constructor <;>
    simp [MME.StothersFourth.Phi233.CyclicExactEdge,
      MME.StothersFourth.Phi233.CyclicAmbientEdge, pow_succ, mul_assoc]
