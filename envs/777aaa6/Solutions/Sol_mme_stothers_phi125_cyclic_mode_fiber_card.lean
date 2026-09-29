-- Prove2me | solution 1 for mme_stothers_phi125_cyclic_mode_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:15:09.959875+00:00
-- url     : https://prove2.me/submissions/c3aad437-d4c0-4f90-b24a-b35d371cbddb

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi125_profile_data
import Theorems.Thm_mme_stothers_phi125_fixed_mode_exact_profile_fiber_card

open BigOperators

set_option autoImplicit false
set_option warningAsError true

private def tripleFiberEquiv
    {A B C D : Type*} (f : A → B) (g : A → C) (h : A → D)
    (x y z : A) :
    {p : A × (A × A) //
      (f p.1, (g p.2.1, h p.2.2)) = (f x, (g y, h z))} ≃
      {a : A // f a = f x} ×
        ({a : A // g a = g y} × {a : A // h a = h z}) where
  toFun p :=
    (⟨p.1.1, congrArg Prod.fst p.2⟩,
      (⟨p.1.2.1, congrArg (fun q ↦ q.2.1) p.2⟩,
        ⟨p.1.2.2, congrArg (fun q ↦ q.2.2) p.2⟩))
  invFun q :=
    ⟨(q.1.1, (q.2.1.1, q.2.2.1)), by
      apply Prod.ext
      · exact q.1.2
      · apply Prod.ext
        · exact q.2.1.2
        · exact q.2.2.2⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv q := by
    rcases q with ⟨q0, q1, q2⟩
    rfl

theorem solution
    (N alpha beta gamma : ℕ) (hsum : alpha + beta + gamma = N)
    (e : MME.StothersFourth.Phi125.CyclicExactEdge
      N alpha beta gamma)
    (i : Fin 3) :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (MME.StothersFourth.Phi125.marginalMultiplicity
          N alpha beta gamma t s).factorial /
          ∏ r : {r : Fin 6 //
              MME.StothersFourth.Phi125.pattern r t = s},
            (MME.StothersFourth.Phi125.profileMultiplicity
              alpha beta gamma r.1).factorial
    Nat.card
        {f : MME.StothersFourth.Phi125.CyclicExactEdge
            N alpha beta gamma //
          MME.StothersFourth.Phi125.cyclicModeWord f i =
            MME.StothersFourth.Phi125.cyclicModeWord e i} =
      D 0 * (D 1 * D 2) := by
  dsimp only
  let A := MME.StothersFourth.Phi125.ExactProfileWord
    N alpha beta gamma
  fin_cases i
  · let equiv := tripleFiberEquiv
      (fun w : A ↦ MME.StothersFourth.Phi125.modeWord w.1 0)
      (fun w : A ↦ MME.StothersFourth.Phi125.modeWord w.1 2)
      (fun w : A ↦ MME.StothersFourth.Phi125.modeWord w.1 1)
      e.1 e.2.1 e.2.2
    change Nat.card
      {p : A × (A × A) //
        ((MME.StothersFourth.Phi125.modeWord p.1.1 0),
          ((MME.StothersFourth.Phi125.modeWord p.2.1.1 2),
            (MME.StothersFourth.Phi125.modeWord p.2.2.1 1))) =
        ((MME.StothersFourth.Phi125.modeWord e.1.1 0),
          ((MME.StothersFourth.Phi125.modeWord e.2.1.1 2),
            (MME.StothersFourth.Phi125.modeWord e.2.2.1 1)))} = _
    rw [Nat.card_congr equiv, Nat.card_prod, Nat.card_prod]
    rw [mme_stothers_phi125_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma hsum e.1 0,
      mme_stothers_phi125_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma hsum e.2.1 2,
      mme_stothers_phi125_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma hsum e.2.2 1]
    ring
  · let equiv := tripleFiberEquiv
      (fun w : A ↦ MME.StothersFourth.Phi125.modeWord w.1 1)
      (fun w : A ↦ MME.StothersFourth.Phi125.modeWord w.1 0)
      (fun w : A ↦ MME.StothersFourth.Phi125.modeWord w.1 2)
      e.1 e.2.1 e.2.2
    change Nat.card
      {p : A × (A × A) //
        ((MME.StothersFourth.Phi125.modeWord p.1.1 1),
          ((MME.StothersFourth.Phi125.modeWord p.2.1.1 0),
            (MME.StothersFourth.Phi125.modeWord p.2.2.1 2))) =
        ((MME.StothersFourth.Phi125.modeWord e.1.1 1),
          ((MME.StothersFourth.Phi125.modeWord e.2.1.1 0),
            (MME.StothersFourth.Phi125.modeWord e.2.2.1 2)))} = _
    rw [Nat.card_congr equiv, Nat.card_prod, Nat.card_prod]
    rw [mme_stothers_phi125_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma hsum e.1 1,
      mme_stothers_phi125_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma hsum e.2.1 0,
      mme_stothers_phi125_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma hsum e.2.2 2]
    ring
  · let equiv := tripleFiberEquiv
      (fun w : A ↦ MME.StothersFourth.Phi125.modeWord w.1 2)
      (fun w : A ↦ MME.StothersFourth.Phi125.modeWord w.1 1)
      (fun w : A ↦ MME.StothersFourth.Phi125.modeWord w.1 0)
      e.1 e.2.1 e.2.2
    change Nat.card
      {p : A × (A × A) //
        ((MME.StothersFourth.Phi125.modeWord p.1.1 2),
          ((MME.StothersFourth.Phi125.modeWord p.2.1.1 1),
            (MME.StothersFourth.Phi125.modeWord p.2.2.1 0))) =
        ((MME.StothersFourth.Phi125.modeWord e.1.1 2),
          ((MME.StothersFourth.Phi125.modeWord e.2.1.1 1),
            (MME.StothersFourth.Phi125.modeWord e.2.2.1 0)))} = _
    rw [Nat.card_congr equiv, Nat.card_prod, Nat.card_prod]
    rw [mme_stothers_phi125_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma hsum e.1 2,
      mme_stothers_phi125_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma hsum e.2.1 1,
      mme_stothers_phi125_fixed_mode_exact_profile_fiber_card
          N alpha beta gamma hsum e.2.2 0]
    ring
