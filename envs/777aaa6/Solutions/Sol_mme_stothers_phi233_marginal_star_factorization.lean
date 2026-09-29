-- Prove2me | solution 1 for mme_stothers_phi233_marginal_star_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:50:32.531936+00:00
-- url     : https://prove2.me/submissions/d6b07e13-d420-4ee2-b226-52fc945600cc

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_marginal_profile_table
import Theorems.Thm_mme_stothers_phi233_fixed_mode_profile_table_fiber_card
import Theorems.Thm_mme_stothers_phi233_profile_table_class_card
import Theorems.Thm_mme_stothers_phi233_marginal_profile_table_constraints

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
set_option warningAsError true

/-- The full same-marginal family is regular over every realized mode word.
Its total cardinality is the mode-word multinomial count times any fixed
mode-star cardinality. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (a : MME.StothersFourth.Phi233.MarginalAddress
      N alpha beta gamma delta) (i : Fin 3) :
    Nat.card
        (MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta) =
      ((2 * N).factorial /
        ∏ s : Fin 5,
          (MME.StothersFourth.Phi233.marginalMultiplicity
            alpha beta gamma delta i s).factorial) *
        Nat.card
          {b : MME.StothersFourth.Phi233.MarginalAddress
              N alpha beta gamma delta // b.1 i = a.1 i} := by
  classical
  let Address := MME.StothersFourth.Phi233.MarginalAddress
    N alpha beta gamma delta
  letI : Fintype (MME.StothersFourth.Phi233.ProfileAddress N) :=
    inferInstanceAs (Fintype (Fin 3 → Fin (2 * N) → Fin 5))
  letI : Fintype Address :=
    inferInstanceAs (Fintype
      {x : MME.StothersFourth.Phi233.ProfileAddress N //
        MME.StothersFourth.Phi233.CoordinatewiseSupported x ∧
          ∀ l : Fin 3, ∀ s : Fin 5,
            ((Finset.univ : Finset (Fin (2 * N))).filter
              (fun j ↦ x l j = s)).card =
              MME.StothersFourth.Phi233.marginalMultiplicity
                alpha beta gamma delta l s})
  let All : Finset Address := Finset.univ
  let Star : Finset Address := All.filter (fun b ↦ b.1 i = a.1 i)
  let Tables : Finset (Fin 10 → ℕ) :=
    All.image MME.StothersFourth.Phi233.marginalProfileTable
  let numerator : ℕ :=
    ∏ s : Fin 5,
      (MME.StothersFourth.Phi233.marginalMultiplicity
        alpha beta gamma delta i s).factorial
  let wordCount : ℕ := (2 * N).factorial / numerator
  have hmarginalTotal :
      (∑ s : Fin 5,
        MME.StothersFourth.Phi233.marginalMultiplicity
          alpha beta gamma delta i s) = 2 * N := by
    calc
      (∑ s : Fin 5,
          MME.StothersFourth.Phi233.marginalMultiplicity
            alpha beta gamma delta i s) =
          ∑ s : Fin 5,
            ((Finset.univ : Finset (Fin (2 * N))).filter
              (fun j ↦ a.1 i j = s)).card := by
        apply Finset.sum_congr rfl
        intro s hs
        exact (a.2.2 i s).symm
      _ = 2 * N := by
        have h := Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ : Finset (Fin (2 * N)))
          (Finset.univ : Finset (Fin 5)) (a.1 i)
        simpa using h
  have hnumDivFact : numerator ∣ (2 * N).factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset (Fin 5))
      (fun s ↦ MME.StothersFourth.Phi233.marginalMultiplicity
        alpha beta gamma delta i s)
    simpa only [numerator, hmarginalTotal] using h
  have hnumPos : 0 < numerator := by
    exact Finset.prod_pos fun s hs ↦ Nat.factorial_pos _
  have hAllPartition :
      (∑ k ∈ Tables,
        (All.filter (fun b ↦
          MME.StothersFourth.Phi233.marginalProfileTable b = k)).card) =
        All.card := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      All Tables MME.StothersFourth.Phi233.marginalProfileTable
    calc
      (∑ k ∈ Tables,
          (All.filter (fun b ↦
            MME.StothersFourth.Phi233.marginalProfileTable b = k)).card) =
          (All.filter (fun b ↦
            MME.StothersFourth.Phi233.marginalProfileTable b ∈ Tables)).card := h
      _ = All.card := by
        congr 1
        apply Finset.filter_eq_self.mpr
        intro b hb
        apply Finset.mem_image.mpr
        exact ⟨b, hb, rfl⟩
  have hStarPartition :
      (∑ k ∈ Tables,
        (Star.filter (fun b ↦
          MME.StothersFourth.Phi233.marginalProfileTable b = k)).card) =
        Star.card := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      Star Tables MME.StothersFourth.Phi233.marginalProfileTable
    have hinside : ∀ b ∈ Star,
        MME.StothersFourth.Phi233.marginalProfileTable b ∈ Tables := by
      intro b hb
      apply Finset.mem_image.mpr
      exact ⟨b, by simp only [All, Finset.mem_univ], rfl⟩
    calc
      (∑ k ∈ Tables,
          (Star.filter (fun b ↦
            MME.StothersFourth.Phi233.marginalProfileTable b = k)).card) =
          (Star.filter (fun b ↦
            MME.StothersFourth.Phi233.marginalProfileTable b ∈ Tables)).card := h
      _ = Star.card := by
        congr 1
        apply Finset.filter_eq_self.mpr
        intro b hb
        exact hinside b hb
  have hclass : ∀ k ∈ Tables,
      (All.filter (fun b ↦
          MME.StothersFourth.Phi233.marginalProfileTable b = k)).card =
        wordCount *
          (Star.filter (fun b ↦
            MME.StothersFourth.Phi233.marginalProfileTable b = k)).card := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨b, hb, hbk⟩
    have hbConstraints :=
      mme_stothers_phi233_marginal_profile_table_constraints
        N alpha beta gamma delta b
    have hkTotal : (∑ r : Fin 10, k r) = 2 * N := by
      rw [← hbk]
      exact hbConstraints.1
    have hkMarginal : ∀ l : Fin 3, ∀ s : Fin 5,
        (∑ r : {r : Fin 10 //
            MME.StothersFourth.Phi233.pattern r l = s}, k r.1) =
          MME.StothersFourth.Phi233.marginalMultiplicity
            alpha beta gamma delta l s := by
      intro l s
      rw [← hbk]
      exact hbConstraints.2 l s
    let TotalClass :=
      {c : Address //
        MME.StothersFourth.Phi233.marginalProfileTable c = k}
    let StarClass :=
      {c : Address // c.1 i = a.1 i ∧
        MME.StothersFourth.Phi233.marginalProfileTable c = k}
    let TotalFiber :=
      {c : Address // c ∈ All.filter (fun b ↦
        MME.StothersFourth.Phi233.marginalProfileTable b = k)}
    let StarFiber :=
      {c : Address // c ∈ Star.filter (fun b ↦
        MME.StothersFourth.Phi233.marginalProfileTable b = k)}
    let eTotal : TotalFiber ≃ TotalClass := {
      toFun c := ⟨c.1, (Finset.mem_filter.mp c.2).2⟩
      invFun c := ⟨c.1, Finset.mem_filter.mpr ⟨by
        simp only [All, Finset.mem_univ], c.2⟩⟩
      left_inv c := by apply Subtype.ext; rfl
      right_inv c := by apply Subtype.ext; rfl
    }
    let eStar : StarFiber ≃ StarClass := {
      toFun c := by
        have hc := Finset.mem_filter.mp c.2
        have hcStar := Finset.mem_filter.mp hc.1
        exact ⟨c.1, hcStar.2, hc.2⟩
      invFun c := ⟨c.1, Finset.mem_filter.mpr ⟨
        Finset.mem_filter.mpr ⟨by
          simp only [All, Finset.mem_univ], c.2.1⟩, c.2.2⟩⟩
      left_inv c := by apply Subtype.ext; rfl
      right_inv c := by apply Subtype.ext; rfl
    }
    have htotalFilter :
        (All.filter (fun b ↦
          MME.StothersFourth.Phi233.marginalProfileTable b = k)).card =
          Nat.card TotalClass := by
      calc
        (All.filter (fun b ↦
            MME.StothersFourth.Phi233.marginalProfileTable b = k)).card =
            Fintype.card TotalFiber := by
          simpa only [TotalFiber] using
            (Fintype.card_coe
              (All.filter (fun b ↦
                MME.StothersFourth.Phi233.marginalProfileTable b = k))).symm
        _ = Nat.card TotalClass := by
          rw [← Nat.card_eq_fintype_card]
          exact Nat.card_congr eTotal
    have hstarFilter :
        (Star.filter (fun b ↦
          MME.StothersFourth.Phi233.marginalProfileTable b = k)).card =
          Nat.card StarClass := by
      calc
        (Star.filter (fun b ↦
            MME.StothersFourth.Phi233.marginalProfileTable b = k)).card =
            Fintype.card StarFiber := by
          simpa only [StarFiber] using
            (Fintype.card_coe
              (Star.filter (fun b ↦
                MME.StothersFourth.Phi233.marginalProfileTable b = k))).symm
        _ = Nat.card StarClass := by
          rw [← Nat.card_eq_fintype_card]
          exact Nat.card_congr eStar
    have htotalClass : Nat.card TotalClass =
        (2 * N).factorial / ∏ r : Fin 10, (k r).factorial := by
      simpa only [TotalClass, Address] using
        (mme_stothers_phi233_profile_table_class_card
          N alpha beta gamma delta k hkTotal hkMarginal)
    have hstarClass : Nat.card StarClass =
        numerator / ∏ r : Fin 10, (k r).factorial := by
      simpa only [StarClass, Address, numerator] using
        (mme_stothers_phi233_fixed_mode_profile_table_fiber_card
          N alpha beta gamma delta a i k hkMarginal)
    have hrowDiv (s : Fin 5) :
        (∏ r : {r : Fin 10 //
            MME.StothersFourth.Phi233.pattern r i = s},
            (k r.1).factorial) ∣
          (MME.StothersFourth.Phi233.marginalMultiplicity
            alpha beta gamma delta i s).factorial := by
      have h := Nat.prod_factorial_dvd_factorial_sum
        (Finset.univ : Finset
          {r : Fin 10 //
            MME.StothersFourth.Phi233.pattern r i = s})
        (fun r ↦ k r.1)
      simpa [hkMarginal i s] using h
    have hdenPartition :
        (∏ s : Fin 5,
          ∏ r : {r : Fin 10 //
              MME.StothersFourth.Phi233.pattern r i = s},
            (k r.1).factorial) =
          ∏ r : Fin 10, (k r).factorial := by
      calc
        (∏ s : Fin 5,
            ∏ r : {r : Fin 10 //
                MME.StothersFourth.Phi233.pattern r i = s},
              (k r.1).factorial) =
            ∏ x : Sigma fun s : Fin 5 ↦
              {r : Fin 10 //
                MME.StothersFourth.Phi233.pattern r i = s},
              (k x.2.1).factorial := by
          exact (Fintype.prod_sigma
            (fun x : Sigma fun s : Fin 5 ↦
              {r : Fin 10 //
                MME.StothersFourth.Phi233.pattern r i = s} ↦
              (k x.2.1).factorial)).symm
        _ = ∏ r : Fin 10, (k r).factorial := by
          simpa only using
            (Equiv.prod_comp
              (Equiv.sigmaFiberEquiv
                (fun r : Fin 10 ↦
                  MME.StothersFourth.Phi233.pattern r i))
              (fun r : Fin 10 ↦ (k r).factorial))
    have hdenDivNum : (∏ r : Fin 10, (k r).factorial) ∣ numerator := by
      rw [← hdenPartition]
      exact Finset.prod_dvd_prod_of_dvd _ _ (by
        intro s hs
        exact hrowDiv s)
    rw [htotalFilter, hstarFilter, htotalClass, hstarClass]
    symm
    calc
      wordCount * (numerator / ∏ r : Fin 10, (k r).factorial) =
          ((2 * N).factorial / numerator) *
            (numerator / ∏ r : Fin 10, (k r).factorial) := by rfl
      _ = (2 * N).factorial * numerator /
          (numerator * ∏ r : Fin 10, (k r).factorial) :=
        Nat.div_mul_div_comm hnumDivFact hdenDivNum
      _ = numerator * (2 * N).factorial /
          (numerator * ∏ r : Fin 10, (k r).factorial) := by
        rw [Nat.mul_comm (2 * N).factorial numerator]
      _ = (2 * N).factorial /
          ∏ r : Fin 10, (k r).factorial :=
        Nat.mul_div_mul_left (2 * N).factorial
          (∏ r : Fin 10, (k r).factorial) hnumPos
  have hcore : All.card = wordCount * Star.card := by
    calc
      All.card = ∑ k ∈ Tables,
          (All.filter (fun b ↦
            MME.StothersFourth.Phi233.marginalProfileTable b = k)).card :=
        hAllPartition.symm
      _ = ∑ k ∈ Tables, wordCount *
          (Star.filter (fun b ↦
            MME.StothersFourth.Phi233.marginalProfileTable b = k)).card := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hclass k hk
      _ = wordCount * ∑ k ∈ Tables,
          (Star.filter (fun b ↦
            MME.StothersFourth.Phi233.marginalProfileTable b = k)).card := by
        rw [Finset.mul_sum]
      _ = wordCount * Star.card := by rw [hStarPartition]
  have hAllNat : Nat.card Address = All.card := by
    calc
      Nat.card Address = Fintype.card Address := Nat.card_eq_fintype_card
      _ = All.card := by simp only [All, Finset.card_univ]
  let StarType := {b : Address // b.1 i = a.1 i}
  let StarCoe := {b : Address // b ∈ Star}
  let eStarFinal : StarType ≃ StarCoe :=
    Equiv.subtypeEquiv (Equiv.refl Address) (fun b ↦ by
      simp only [Star, All, Finset.mem_filter, Finset.mem_univ,
        true_and, Equiv.refl_apply])
  have hStarNat : Nat.card StarType = Star.card := by
    calc
      Nat.card StarType = Nat.card StarCoe := Nat.card_congr eStarFinal
      _ = Fintype.card StarCoe := Nat.card_eq_fintype_card
      _ = Star.card := Fintype.card_coe Star
  simpa only [Address, numerator, wordCount, StarType,
    hAllNat, hStarNat] using hcore
