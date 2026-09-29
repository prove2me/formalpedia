-- Prove2me | solution 1 for mme_stothers_phi224_marginal_star_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:34:50.610796+00:00
-- url     : https://prove2.me/submissions/b072b1fc-f399-489f-bbbd-caada9d27f49

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_stothers_phi224_profile_histogram_class_card
import Theorems.Thm_mme_stothers_phi224_fixed_mode_histogram_fiber_card

open BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
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
    left_inv a := by apply Subtype.ext; rfl
    right_inv a := by
      rcases a with ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
      cases ha
      rfl
  }
  rw [Fintype.card_congr e, Fintype.card_sigma]

/-- The whole same-marginal phi_224 family is regular over the realized
grade words in each tensor mode. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (a : MME.StothersFourth.Phi224.MarginalProfileWord
      N alpha beta gamma delta) (i : Fin 3) :
    Nat.card
        (MME.StothersFourth.Phi224.MarginalProfileWord
          N alpha beta gamma delta) =
      ((2 * N).factorial /
        ∏ s : Fin 5,
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s).factorial) *
        Nat.card
          {b : MME.StothersFourth.Phi224.MarginalProfileWord
              N alpha beta gamma delta //
            MME.StothersFourth.Phi224.modeWord b.1 i =
              MME.StothersFourth.Phi224.modeWord a.1 i} := by
  classical
  let Address := MME.StothersFourth.Phi224.MarginalProfileWord
    N alpha beta gamma delta
  letI : Fintype Address :=
    @Subtype.fintype _ _ (Classical.decPred _) Pi.instFintype
  let histogram : Address → Fin 9 → ℕ := fun b r ↦
    Fintype.card {j : Fin (2 * N) // b.1 j = r}
  let All : Finset Address := Finset.univ
  let Star : Finset Address := All.filter (fun b ↦
    MME.StothersFourth.Phi224.modeWord b.1 i =
      MME.StothersFourth.Phi224.modeWord a.1 i)
  let Tables : Finset (Fin 9 → ℕ) := All.image histogram
  let numerator : ℕ :=
    ∏ s : Fin 5,
      (MME.StothersFourth.Phi224.marginalMultiplicity
        alpha beta gamma delta i s).factorial
  let wordCount : ℕ := (2 * N).factorial / numerator
  have hmarginalTotal :
      (∑ s : Fin 5,
        MME.StothersFourth.Phi224.marginalMultiplicity
          alpha beta gamma delta i s) = 2 * N := by
    calc
      (∑ s : Fin 5,
          MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s) =
          ∑ s : Fin 5,
            ((Finset.univ : Finset (Fin (2 * N))).filter
              (fun j ↦ MME.StothersFourth.Phi224.modeWord a.1 i j = s)).card := by
        apply Finset.sum_congr rfl
        intro s hs
        exact (a.2 i s).symm
      _ = 2 * N := by
        have h := Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ : Finset (Fin (2 * N)))
          (Finset.univ : Finset (Fin 5))
          (MME.StothersFourth.Phi224.modeWord a.1 i)
        simpa using h
  have hnumDivFact : numerator ∣ (2 * N).factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset (Fin 5))
      (fun s ↦ MME.StothersFourth.Phi224.marginalMultiplicity
        alpha beta gamma delta i s)
    simpa only [numerator, hmarginalTotal] using h
  have hnumPos : 0 < numerator := by
    exact Finset.prod_pos fun s hs ↦ Nat.factorial_pos _
  have hAllPartition :
      (∑ k ∈ Tables,
        (All.filter (fun b ↦ histogram b = k)).card) = All.card := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      All Tables histogram
    calc
      (∑ k ∈ Tables,
          (All.filter (fun b ↦ histogram b = k)).card) =
          (All.filter (fun b ↦ histogram b ∈ Tables)).card := h
      _ = All.card := by
        congr 1
        apply Finset.filter_eq_self.mpr
        intro b hb
        exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hStarPartition :
      (∑ k ∈ Tables,
        (Star.filter (fun b ↦ histogram b = k)).card) = Star.card := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      Star Tables histogram
    have hinside : ∀ b ∈ Star, histogram b ∈ Tables := by
      intro b hb
      exact Finset.mem_image.mpr ⟨b, by simp only [All, Finset.mem_univ], rfl⟩
    calc
      (∑ k ∈ Tables,
          (Star.filter (fun b ↦ histogram b = k)).card) =
          (Star.filter (fun b ↦ histogram b ∈ Tables)).card := h
      _ = Star.card := by
        congr 1
        apply Finset.filter_eq_self.mpr
        intro b hb
        exact hinside b hb
  have hclass : ∀ k ∈ Tables,
      (All.filter (fun b ↦ histogram b = k)).card =
        wordCount *
          (Star.filter (fun b ↦ histogram b = k)).card := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨b, hb, hbk⟩
    have hkTotal : (∑ r : Fin 9, k r) = 2 * N := by
      rw [← hbk]
      calc
        (∑ r : Fin 9, histogram b r) =
            ∑ r : Fin 9,
              ((Finset.univ : Finset (Fin (2 * N))).filter
                (fun j ↦ b.1 j = r)).card := by
          apply Finset.sum_congr rfl
          intro r hr
          exact Fintype.card_subtype _
        _ = 2 * N := by
          have h := Finset.sum_card_fiberwise_eq_card_filter
            (Finset.univ : Finset (Fin (2 * N)))
            (Finset.univ : Finset (Fin 9)) b.1
          simpa using h
    have hkMarginal : ∀ l : Fin 3, ∀ s : Fin 5,
        (∑ r : {r : Fin 9 //
            MME.StothersFourth.Phi224.pattern r l = s}, k r.1) =
          MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta l s := by
      intro l s
      rw [← hbk]
      calc
        (∑ r : {r : Fin 9 //
            MME.StothersFourth.Phi224.pattern r l = s},
              histogram b r.1) =
            Fintype.card {j : Fin (2 * N) //
              MME.StothersFourth.Phi224.pattern (b.1 j) l = s} := by
          rw [card_composite_fiber b.1
            (fun r : Fin 9 ↦
              MME.StothersFourth.Phi224.pattern r l) s]
        _ = ((Finset.univ : Finset (Fin (2 * N))).filter
              (fun j ↦ MME.StothersFourth.Phi224.modeWord b.1 l j = s)).card := by
          rw [Fintype.card_subtype]
          rfl
        _ = MME.StothersFourth.Phi224.marginalMultiplicity
              alpha beta gamma delta l s := b.2 l s
    let TotalClass := {c : Address // ∀ r : Fin 9, histogram c r = k r}
    let StarClass := {c : Address //
      MME.StothersFourth.Phi224.modeWord c.1 i =
          MME.StothersFourth.Phi224.modeWord a.1 i ∧
        ∀ r : Fin 9, histogram c r = k r}
    let TotalFiber := {c : Address // c ∈
      All.filter (fun b ↦ histogram b = k)}
    let StarFiber := {c : Address // c ∈
      Star.filter (fun b ↦ histogram b = k)}
    let eTotal : TotalFiber ≃ TotalClass := {
      toFun c := ⟨c.1, congrFun (Finset.mem_filter.mp c.2).2⟩
      invFun c := ⟨c.1, Finset.mem_filter.mpr ⟨by
        simp only [All, Finset.mem_univ], funext c.2⟩⟩
      left_inv c := by apply Subtype.ext; rfl
      right_inv c := by apply Subtype.ext; rfl
    }
    let eStar : StarFiber ≃ StarClass := {
      toFun c := by
        have hc := Finset.mem_filter.mp c.2
        have hcStar := Finset.mem_filter.mp hc.1
        exact ⟨c.1, hcStar.2, congrFun hc.2⟩
      invFun c := ⟨c.1, Finset.mem_filter.mpr ⟨
        Finset.mem_filter.mpr ⟨by
          simp only [All, Finset.mem_univ], c.2.1⟩,
        funext c.2.2⟩⟩
      left_inv c := by apply Subtype.ext; rfl
      right_inv c := by apply Subtype.ext; rfl
    }
    have htotalFilter :
        (All.filter (fun b ↦ histogram b = k)).card =
          Nat.card TotalClass := by
      calc
        (All.filter (fun b ↦ histogram b = k)).card =
            Fintype.card TotalFiber := by
          simpa only [TotalFiber] using
            (Fintype.card_coe
              (All.filter (fun b ↦ histogram b = k))).symm
        _ = Nat.card TotalClass := by
          rw [← Nat.card_eq_fintype_card]
          exact Nat.card_congr eTotal
    have hstarFilter :
        (Star.filter (fun b ↦ histogram b = k)).card =
          Nat.card StarClass := by
      calc
        (Star.filter (fun b ↦ histogram b = k)).card =
            Fintype.card StarFiber := by
          simpa only [StarFiber] using
            (Fintype.card_coe
              (Star.filter (fun b ↦ histogram b = k))).symm
        _ = Nat.card StarClass := by
          rw [← Nat.card_eq_fintype_card]
          exact Nat.card_congr eStar
    have htotalClass : Nat.card TotalClass =
        (2 * N).factorial / ∏ r : Fin 9, (k r).factorial := by
      simpa only [TotalClass, Address, histogram] using
        (mme_stothers_phi224_profile_histogram_class_card
          N alpha beta gamma delta k hkTotal hkMarginal)
    have hstarClass : Nat.card StarClass =
        numerator / ∏ r : Fin 9, (k r).factorial := by
      simpa only [StarClass, Address, histogram, numerator] using
        (mme_stothers_phi224_fixed_mode_histogram_fiber_card
          N alpha beta gamma delta a i k hkMarginal)
    have hrowDiv (s : Fin 5) :
        (∏ r : {r : Fin 9 //
            MME.StothersFourth.Phi224.pattern r i = s},
            (k r.1).factorial) ∣
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s).factorial := by
      have h := Nat.prod_factorial_dvd_factorial_sum
        (Finset.univ : Finset
          {r : Fin 9 //
            MME.StothersFourth.Phi224.pattern r i = s})
        (fun r ↦ k r.1)
      simpa [hkMarginal i s] using h
    have hdenPartition :
        (∏ s : Fin 5,
          ∏ r : {r : Fin 9 //
              MME.StothersFourth.Phi224.pattern r i = s},
            (k r.1).factorial) =
          ∏ r : Fin 9, (k r).factorial := by
      calc
        (∏ s : Fin 5,
            ∏ r : {r : Fin 9 //
                MME.StothersFourth.Phi224.pattern r i = s},
              (k r.1).factorial) =
            ∏ x : Sigma fun s : Fin 5 ↦
              {r : Fin 9 //
                MME.StothersFourth.Phi224.pattern r i = s},
              (k x.2.1).factorial := by
          exact (Fintype.prod_sigma
            (fun x : Sigma fun s : Fin 5 ↦
              {r : Fin 9 //
                MME.StothersFourth.Phi224.pattern r i = s} ↦
              (k x.2.1).factorial)).symm
        _ = ∏ r : Fin 9, (k r).factorial := by
          simpa only using
            (Equiv.prod_comp
              (Equiv.sigmaFiberEquiv
                (fun r : Fin 9 ↦
                  MME.StothersFourth.Phi224.pattern r i))
              (fun r : Fin 9 ↦ (k r).factorial))
    have hdenDivNum : (∏ r : Fin 9, (k r).factorial) ∣ numerator := by
      rw [← hdenPartition]
      exact Finset.prod_dvd_prod_of_dvd _ _ (by
        intro s hs
        exact hrowDiv s)
    rw [htotalFilter, hstarFilter, htotalClass, hstarClass]
    symm
    calc
      wordCount * (numerator / ∏ r : Fin 9, (k r).factorial) =
          ((2 * N).factorial / numerator) *
            (numerator / ∏ r : Fin 9, (k r).factorial) := by rfl
      _ = (2 * N).factorial * numerator /
          (numerator * ∏ r : Fin 9, (k r).factorial) :=
        Nat.div_mul_div_comm hnumDivFact hdenDivNum
      _ = numerator * (2 * N).factorial /
          (numerator * ∏ r : Fin 9, (k r).factorial) := by
        rw [Nat.mul_comm (2 * N).factorial numerator]
      _ = (2 * N).factorial /
          ∏ r : Fin 9, (k r).factorial :=
        Nat.mul_div_mul_left (2 * N).factorial
          (∏ r : Fin 9, (k r).factorial) hnumPos
  have hcore : All.card = wordCount * Star.card := by
    calc
      All.card = ∑ k ∈ Tables,
          (All.filter (fun b ↦ histogram b = k)).card :=
        hAllPartition.symm
      _ = ∑ k ∈ Tables, wordCount *
          (Star.filter (fun b ↦ histogram b = k)).card := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hclass k hk
      _ = wordCount * ∑ k ∈ Tables,
          (Star.filter (fun b ↦ histogram b = k)).card := by
        rw [Finset.mul_sum]
      _ = wordCount * Star.card := by rw [hStarPartition]
  have hAllNat : Nat.card Address = All.card := by
    calc
      Nat.card Address = Fintype.card Address := Nat.card_eq_fintype_card
      _ = All.card := by simp only [All, Finset.card_univ]
  let StarType := {b : Address //
    MME.StothersFourth.Phi224.modeWord b.1 i =
      MME.StothersFourth.Phi224.modeWord a.1 i}
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
