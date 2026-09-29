-- Prove2me | solution 1 for mme_stothers_phi233_marginal_profile_table_constraints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:42:17.841451+00:00
-- url     : https://prove2.me/submissions/607d7c30-bad3-4bd7-b496-ccee64766cb8

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_marginal_profile_table

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

private theorem card_composite_fiber
    {alpha beta iota : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta] [DecidableEq iota]
    (g : alpha → beta) (q : beta → iota) (i : iota) :
    Fintype.card {a : alpha // q (g a) = i} =
      ∑ b : {b : beta // q b = i},
        Fintype.card {a : alpha // g a = b.1} := by
  classical
  let e : {a : alpha // q (g a) = i} ≃
      Sigma fun b : {b : beta // q b = i} ↦
        {a : alpha // g a = b.1} := {
    toFun a := ⟨⟨g a.1, a.2⟩, ⟨a.1, rfl⟩⟩
    invFun a := ⟨a.2.1, by rw [a.2.2, a.1.2]⟩
    left_inv a := by
      apply Subtype.ext
      rfl
    right_inv a := by
      rcases a with ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
      cases ha
      rfl
  }
  rw [Fintype.card_congr e, Fintype.card_sigma]

/-- Every joint profile table arising from a same-marginal address has the
correct total and all three prescribed five-grade projections. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (a : MME.StothersFourth.Phi233.MarginalAddress
      N alpha beta gamma delta) :
    (∑ r : Fin 10,
      MME.StothersFourth.Phi233.marginalProfileTable a r) = 2 * N ∧
    ∀ l : Fin 3, ∀ s : Fin 5,
      (∑ r : {r : Fin 10 //
          MME.StothersFourth.Phi233.pattern r l = s},
        MME.StothersFourth.Phi233.marginalProfileTable a r.1) =
      MME.StothersFourth.Phi233.marginalMultiplicity
        alpha beta gamma delta l s := by
  classical
  constructor
  · change (∑ r : Fin 10,
      Fintype.card {j : Fin (2 * N) //
        MME.StothersFourth.Phi233.marginalLabelAt a j = r}) = 2 * N
    simp_rw [Fintype.card_subtype]
    have h := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin (2 * N)))
      (Finset.univ : Finset (Fin 10))
      (MME.StothersFourth.Phi233.marginalLabelAt a)
    simpa using h
  · intro l s
    change (∑ r : {r : Fin 10 //
        MME.StothersFourth.Phi233.pattern r l = s},
      Fintype.card {j : Fin (2 * N) //
        MME.StothersFourth.Phi233.marginalLabelAt a j = r.1}) = _
    rw [← card_composite_fiber
      (MME.StothersFourth.Phi233.marginalLabelAt a)
      (fun r : Fin 10 ↦ MME.StothersFourth.Phi233.pattern r l) s]
    rw [Fintype.card_subtype]
    calc
      ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦
            MME.StothersFourth.Phi233.pattern
              (MME.StothersFourth.Phi233.marginalLabelAt a j) l = s)).card =
          ((Finset.univ : Finset (Fin (2 * N))).filter
            (fun j ↦ a.1 l j = s)).card := by
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← congrFun
          (MME.StothersFourth.Phi233.addressType_marginalLabelAt a j) l]
        rfl
      _ = MME.StothersFourth.Phi233.marginalMultiplicity
            alpha beta gamma delta l s := a.2.2 l s
