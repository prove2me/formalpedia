-- Prove2me | solution 1 for mme_stothers_phi233_exact_profile_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:11:51.809819+00:00
-- url     : https://prove2.me/submissions/12add50c-1859-4041-a22a-30b9abc4b0c5

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_CW_square_five_grade_certificate
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Theorems.Thm_mme_stothers_phi233_pattern_injective

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option warningAsError true

theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : 2 * alpha + beta + gamma + delta = N) :
    Nat.card
        (MME.StothersFourth.Phi233.ExactProfileAddress
          N alpha beta gamma delta) =
      (2 * N).factorial /
        ∏ r : Fin 10,
          (MME.StothersFourth.Phi233.profileMultiplicity
            alpha beta gamma delta r).factorial := by
  classical
  let multiplicity : Fin 10 → ℕ :=
    MME.StothersFourth.Phi233.profileMultiplicity alpha beta gamma delta
  have htotal : (∑ r : Fin 10, multiplicity r) = 2 * N := by
    simp [multiplicity, MME.StothersFourth.Phi233.profileMultiplicity,
      Fin.sum_univ_succ]
    omega
  have htotalCard :
      (∑ r : Fin 10, multiplicity r) = Fintype.card (Fin (2 * N)) := by
    simpa using htotal
  have hpattern : Function.Injective MME.StothersFourth.Phi233.pattern :=
    mme_stothers_phi233_pattern_injective
  let labelAt
      (a : MME.StothersFourth.Phi233.ExactProfileAddress
        N alpha beta gamma delta)
      (j : Fin (2 * N)) : Fin 10 :=
    Classical.choose (a.1.2.1 j)
  have hlabelAt : ∀
      (a : MME.StothersFourth.Phi233.ExactProfileAddress
        N alpha beta gamma delta) (j : Fin (2 * N)),
      MME.StothersFourth.Phi233.addressType a.1.1 j =
        MME.StothersFourth.Phi233.pattern (labelAt a j) := by
    intro a j
    exact Classical.choose_spec (a.1.2.1 j)
  let Assignment :=
    {g : Fin (2 * N) → Fin 10 //
      ∀ r, Fintype.card {j // g j = r} = multiplicity r}
  have assignmentMarginal : ∀ G : Assignment,
      ∀ i : Fin 3, ∀ k : Fin 5,
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ MME.StothersFourth.Phi233.pattern (G.1 j) i = k)).card =
          MME.StothersFourth.Phi233.marginalMultiplicity
            alpha beta gamma delta i k := by
    intro G i k
    have hgfiber : ∀ r : Fin 10,
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ G.1 j = r)).card = multiplicity r := by
      intro r
      rw [← Fintype.card_subtype]
      exact G.2 r
    calc
      ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ MME.StothersFourth.Phi233.pattern (G.1 j) i = k)).card =
          ((Finset.univ : Finset (Fin (2 * N))).filter
            (fun j ↦ G.1 j ∈
              (Finset.univ : Finset (Fin 10)).filter
                (fun r ↦ MME.StothersFourth.Phi233.pattern r i = k))).card := by
            congr 1
            ext j
            simp
      _ = ∑ r ∈ (Finset.univ : Finset (Fin 10)).filter
            (fun r ↦ MME.StothersFourth.Phi233.pattern r i = k),
            ((Finset.univ : Finset (Fin (2 * N))).filter
              (fun j ↦ G.1 j = r)).card := by
            symm
            exact Finset.sum_card_fiberwise_eq_card_filter
              (Finset.univ : Finset (Fin (2 * N)))
              ((Finset.univ : Finset (Fin 10)).filter
                (fun r ↦ MME.StothersFourth.Phi233.pattern r i = k)) G.1
      _ = ∑ r ∈ (Finset.univ : Finset (Fin 10)).filter
            (fun r ↦ MME.StothersFourth.Phi233.pattern r i = k),
            multiplicity r := by
            apply Finset.sum_congr rfl
            intro r hr
            exact hgfiber r
      _ = ∑ r : Fin 10,
            if MME.StothersFourth.Phi233.pattern r i = k then
              multiplicity r else 0 := by
            exact Finset.sum_filter
              (fun r : Fin 10 ↦
                MME.StothersFourth.Phi233.pattern r i = k)
              multiplicity
      _ = MME.StothersFourth.Phi233.marginalMultiplicity
            alpha beta gamma delta i k := by
            fin_cases i <;> fin_cases k <;>
              simp [multiplicity,
                MME.StothersFourth.Phi233.pattern,
                MME.StothersFourth.Phi233.profileMultiplicity,
                MME.StothersFourth.Phi233.marginalMultiplicity,
                MME.cwSquareBlockType, Fin.sum_univ_succ] <;> omega
  let e :
      MME.StothersFourth.Phi233.ExactProfileAddress
          N alpha beta gamma delta ≃ Assignment :=
    { toFun := fun a ↦ ⟨labelAt a, by
        intro r
        rw [Fintype.card_subtype]
        calc
          ((Finset.univ : Finset (Fin (2 * N))).filter
              (fun j ↦ labelAt a j = r)).card =
              ((Finset.univ : Finset (Fin (2 * N))).filter
                (fun j ↦
                  MME.StothersFourth.Phi233.addressType a.1.1 j =
                    MME.StothersFourth.Phi233.pattern r)).card := by
                congr 1
                ext j
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                constructor
                · intro hj
                  rw [hlabelAt a j, hj]
                · intro hj
                  exact hpattern (Eq.trans (hlabelAt a j).symm hj)
          _ = multiplicity r := by
                exact a.2 r⟩
      invFun := fun G ↦ by
        let x : MME.StothersFourth.Phi233.ProfileAddress N :=
          fun i j ↦ MME.StothersFourth.Phi233.pattern (G.1 j) i
        have hsupported :
            MME.StothersFourth.Phi233.CoordinatewiseSupported x := by
          intro j
          exact ⟨G.1 j, rfl⟩
        have hmarginal : ∀ i : Fin 3, ∀ k : Fin 5,
            ((Finset.univ : Finset (Fin (2 * N))).filter
              (fun j ↦ x i j = k)).card =
                MME.StothersFourth.Phi233.marginalMultiplicity
                  alpha beta gamma delta i k := by
          intro i k
          exact assignmentMarginal G i k
        let xm : MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta := ⟨x, hsupported, hmarginal⟩
        refine ⟨xm, ?_⟩
        intro r
        have hgfiber :
            ((Finset.univ : Finset (Fin (2 * N))).filter
              (fun j ↦ G.1 j = r)).card = multiplicity r := by
          rw [← Fintype.card_subtype]
          exact G.2 r
        calc
          ((Finset.univ : Finset (Fin (2 * N))).filter
              (fun j ↦
                MME.StothersFourth.Phi233.addressType (Subtype.val xm) j =
                  MME.StothersFourth.Phi233.pattern r)).card =
              ((Finset.univ : Finset (Fin (2 * N))).filter
                (fun j ↦ G.1 j = r)).card := by
                congr 1
                ext j
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                change
                  MME.StothersFourth.Phi233.pattern (G.1 j) =
                      MME.StothersFourth.Phi233.pattern r ↔
                    G.1 j = r
                exact hpattern.eq_iff
          _ = multiplicity r := hgfiber
          _ = MME.StothersFourth.Phi233.profileMultiplicity
                alpha beta gamma delta r := rfl
      left_inv := by
        intro a
        apply Subtype.ext
        apply Subtype.ext
        funext i j
        exact congrFun (hlabelAt a j).symm i
      right_inv := by
        intro G
        apply Subtype.ext
        funext j
        apply hpattern
        exact (hlabelAt _ j).symm }
  let ftGeneric : Fintype Assignment :=
    @Subtype.fintype _ _
      (fun _ ↦ Fintype.decidableForallFintype) Pi.instFintype
  have hcountGeneric : @Fintype.card Assignment ftGeneric =
      (2 * N).factorial /
        ∏ r : Fin 10, (multiplicity r).factorial := by
    simpa only [Assignment, Fintype.card_fin] using
      (mme_fintype_prescribed_fiber_function_card
        (α := Fin (2 * N)) (ι := Fin 10) multiplicity htotalCard)
  have hcountNat : Nat.card Assignment =
      (2 * N).factorial /
        ∏ r : Fin 10, (multiplicity r).factorial := by
    calc
      Nat.card Assignment = @Fintype.card Assignment inferInstance :=
        Nat.card_eq_fintype_card
      _ = @Fintype.card Assignment ftGeneric :=
        @Fintype.card_congr Assignment Assignment inferInstance ftGeneric
          (Equiv.refl Assignment)
      _ = _ := hcountGeneric
  calc
    Nat.card
        (MME.StothersFourth.Phi233.ExactProfileAddress
          N alpha beta gamma delta) = Nat.card Assignment :=
      Nat.card_congr e
    _ = (2 * N).factorial / ∏ r : Fin 10, (multiplicity r).factorial := by
      exact hcountNat
    _ = (2 * N).factorial /
        ∏ r : Fin 10,
          (MME.StothersFourth.Phi233.profileMultiplicity
            alpha beta gamma delta r).factorial := rfl
