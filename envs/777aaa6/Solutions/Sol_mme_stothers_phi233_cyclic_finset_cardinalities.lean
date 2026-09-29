-- Prove2me | solution 1 for mme_stothers_phi233_cyclic_finset_cardinalities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:48:05.911559+00:00
-- url     : https://prove2.me/submissions/c9fb662e-5f78-4310-aea5-92ccf3aea637

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_finsets

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (N alpha beta gamma delta : ℕ) :
    MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta ⊆
      MME.StothersFourth.Phi233.ambientFinset
        N alpha beta gamma delta ∧
    (MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta).card =
      (Nat.card
        (MME.StothersFourth.Phi233.ExactProfileAddress
          N alpha beta gamma delta)) ^ 3 ∧
    (MME.StothersFourth.Phi233.ambientFinset
        N alpha beta gamma delta).card =
      (Nat.card
        (MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta)) ^ 3 := by
  classical
  let ftExact :=
    MME.StothersFourth.Phi233.cyclicExactEdgeFintype
      N alpha beta gamma delta
  let ftAmbient :=
    MME.StothersFourth.Phi233.cyclicAmbientEdgeFintype
      N alpha beta gamma delta
  have htarget :
      (MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta).card =
        Nat.card
          (MME.StothersFourth.Phi233.CyclicExactEdge
            N alpha beta gamma delta) := by
    calc
      (MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta).card =
          (@Finset.univ
            (MME.StothersFourth.Phi233.CyclicExactEdge
              N alpha beta gamma delta) ftExact).card := by
        exact Finset.card_map _
      _ = @Fintype.card
          (MME.StothersFourth.Phi233.CyclicExactEdge
            N alpha beta gamma delta) ftExact := Finset.card_univ
      _ = Nat.card
          (MME.StothersFourth.Phi233.CyclicExactEdge
            N alpha beta gamma delta) := Nat.card_eq_fintype_card.symm
  have hambient :
      (MME.StothersFourth.Phi233.ambientFinset
        N alpha beta gamma delta).card =
        Nat.card
          (MME.StothersFourth.Phi233.CyclicAmbientEdge
            N alpha beta gamma delta) := by
    calc
      (MME.StothersFourth.Phi233.ambientFinset
          N alpha beta gamma delta).card =
          (@Finset.univ
            (MME.StothersFourth.Phi233.CyclicAmbientEdge
              N alpha beta gamma delta) ftAmbient).card := rfl
      _ = @Fintype.card
          (MME.StothersFourth.Phi233.CyclicAmbientEdge
            N alpha beta gamma delta) ftAmbient := Finset.card_univ
      _ = Nat.card
          (MME.StothersFourth.Phi233.CyclicAmbientEdge
            N alpha beta gamma delta) := Nat.card_eq_fintype_card.symm
  refine ⟨?_, ?_, ?_⟩
  · intro e _
    simp only [MME.StothersFourth.Phi233.ambientFinset,
      Finset.mem_univ]
  · rw [htarget]
    simp [MME.StothersFourth.Phi233.CyclicExactEdge, pow_succ, mul_assoc]
  · rw [hambient]
    simp [MME.StothersFourth.Phi233.CyclicAmbientEdge, pow_succ, mul_assoc]
