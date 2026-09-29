-- Prove2me | solution 1 for mme_stothers_phi233_profile_table_class_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:42:17.91273+00:00
-- url     : https://prove2.me/submissions/bf098a3e-876f-49f7-8d99-65dfcd00a0f3

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_marginal_profile_table
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Theorems.Thm_mme_stothers_phi233_pattern_injective

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
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

/-- Exact cardinality of one compatible ten-pattern table stratum in the
full same-marginal `phi_233` family. -/
theorem solution
    (N alpha beta gamma delta : ℕ) (k : Fin 10 → ℕ)
    (hkTotal : (∑ r : Fin 10, k r) = 2 * N)
    (hkMarginal : ∀ l : Fin 3, ∀ s : Fin 5,
      (∑ r : {r : Fin 10 //
          MME.StothersFourth.Phi233.pattern r l = s}, k r.1) =
        MME.StothersFourth.Phi233.marginalMultiplicity
          alpha beta gamma delta l s) :
    Nat.card
        {b : MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta //
          MME.StothersFourth.Phi233.marginalProfileTable b = k} =
      (2 * N).factorial / ∏ r : Fin 10, (k r).factorial := by
  classical
  let Assignment :=
    {g : Fin (2 * N) → Fin 10 //
      ∀ r, Fintype.card {j // g j = r} = k r}
  let AddressClass :=
    {b : MME.StothersFourth.Phi233.MarginalAddress
        N alpha beta gamma delta //
      MME.StothersFourth.Phi233.marginalProfileTable b = k}
  have hpattern :
      Function.Injective MME.StothersFourth.Phi233.pattern :=
    mme_stothers_phi233_pattern_injective
  let e : AddressClass ≃ Assignment := {
    toFun b :=
      ⟨MME.StothersFourth.Phi233.marginalLabelAt b.1, by
        intro r
        exact congrFun b.2 r⟩
    invFun G := by
      let raw : MME.StothersFourth.Phi233.ProfileAddress N :=
        fun l j ↦ MME.StothersFourth.Phi233.pattern (G.1 j) l
      have hsupport :
          MME.StothersFourth.Phi233.CoordinatewiseSupported raw := by
        intro j
        exact ⟨G.1 j, rfl⟩
      have hmarginal : ∀ l : Fin 3, ∀ s : Fin 5,
          ((Finset.univ : Finset (Fin (2 * N))).filter
            (fun j ↦ raw l j = s)).card =
            MME.StothersFourth.Phi233.marginalMultiplicity
              alpha beta gamma delta l s := by
        intro l s
        rw [← Fintype.card_subtype]
        change Fintype.card {j : Fin (2 * N) //
          MME.StothersFourth.Phi233.pattern (G.1 j) l = s} = _
        rw [card_composite_fiber G.1
          (fun r : Fin 10 ↦
            MME.StothersFourth.Phi233.pattern r l) s]
        calc
          (∑ r : {r : Fin 10 //
              MME.StothersFourth.Phi233.pattern r l = s},
              Fintype.card {j : Fin (2 * N) // G.1 j = r.1}) =
              ∑ r : {r : Fin 10 //
                MME.StothersFourth.Phi233.pattern r l = s},
                k r.1 := by
            apply Finset.sum_congr rfl
            intro r hr
            exact G.2 r.1
          _ = MME.StothersFourth.Phi233.marginalMultiplicity
                alpha beta gamma delta l s := hkMarginal l s
      let b : MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta := ⟨raw, hsupport, hmarginal⟩
      refine ⟨b, ?_⟩
      funext r
      change Fintype.card
        {j : Fin (2 * N) //
          MME.StothersFourth.Phi233.marginalLabelAt b j = r} = k r
      calc
        Fintype.card
            {j : Fin (2 * N) //
              MME.StothersFourth.Phi233.marginalLabelAt b j = r} =
            Fintype.card {j : Fin (2 * N) // G.1 j = r} := by
          apply Fintype.card_congr
          exact Equiv.subtypeEquiv (Equiv.refl _)
            (fun j ↦ by
              have hj :
                  MME.StothersFourth.Phi233.marginalLabelAt b j =
                    G.1 j := by
                apply hpattern
                rw [← MME.StothersFourth.Phi233.addressType_marginalLabelAt]
                rfl
              simp only [Equiv.refl_apply, hj])
        _ = k r := G.2 r
    left_inv b := by
      apply Subtype.ext
      apply Subtype.ext
      funext l j
      exact congrFun
        (MME.StothersFourth.Phi233.addressType_marginalLabelAt b.1 j).symm l
    right_inv G := by
      apply Subtype.ext
      funext j
      apply hpattern
      rw [← MME.StothersFourth.Phi233.addressType_marginalLabelAt]
      rfl
  }
  have htotalCard :
      (∑ r : Fin 10, k r) = Fintype.card (Fin (2 * N)) := by
    simpa using hkTotal
  let ftGeneric : Fintype Assignment :=
    @Subtype.fintype _ _
      (fun _ ↦ Fintype.decidableForallFintype) Pi.instFintype
  have hcountGeneric : @Fintype.card Assignment ftGeneric =
      (2 * N).factorial / ∏ r : Fin 10, (k r).factorial := by
    simpa only [Assignment, Fintype.card_fin] using
      (mme_fintype_prescribed_fiber_function_card
        (α := Fin (2 * N)) (ι := Fin 10) k htotalCard)
  have hassignment : Nat.card Assignment =
      (2 * N).factorial / ∏ r : Fin 10, (k r).factorial := by
    calc
      Nat.card Assignment = @Fintype.card Assignment inferInstance :=
        Nat.card_eq_fintype_card
      _ = @Fintype.card Assignment ftGeneric :=
        @Fintype.card_congr Assignment Assignment inferInstance ftGeneric
          (Equiv.refl Assignment)
      _ = _ := hcountGeneric
  calc
    Nat.card AddressClass = Nat.card Assignment := Nat.card_congr e
    _ = (2 * N).factorial / ∏ r : Fin 10, (k r).factorial :=
      hassignment
