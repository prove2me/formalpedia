-- Prove2me | solution 1 for mme_stothers_phi224_exact_star_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:34:50.586704+00:00
-- url     : https://prove2.me/submissions/52740877-e4e5-4f5f-a0bf-e319572e14a3

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_stothers_phi224_exact_profile_card
import Theorems.Thm_mme_stothers_phi224_exact_profile_marginals
import Theorems.Thm_mme_stothers_phi224_fixed_mode_exact_profile_fiber_card

open BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option warningAsError true

private theorem sum_ite_eq_sum_subtype
    {beta iota M : Type*} [Fintype beta] [DecidableEq iota]
    [AddCommMonoid M] (q : beta → iota) (i : iota) (f : beta → M) :
    (∑ b : beta, if q b = i then f b else 0) =
      ∑ b : {b : beta // q b = i}, f b.1 := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    ((Finset.univ : Finset beta).filter (fun b ↦ q b = i))
    (fun b ↦ by simp) f

private theorem prod_nat_div_eq_div_prod_of_dvd
    {iota : Type*} (s : Finset iota) (A B : iota → ℕ)
    (hdiv : ∀ i ∈ s, B i ∣ A i) :
    (∏ i ∈ s, A i / B i) =
      (∏ i ∈ s, A i) / ∏ i ∈ s, B i := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
      have haDiv : B a ∣ A a := hdiv a (by simp)
      have hsDiv : ∀ i ∈ s, B i ∣ A i := by
        intro i hi
        exact hdiv i (by simp [hi])
      have hprodDiv : (∏ i ∈ s, B i) ∣ ∏ i ∈ s, A i :=
        Finset.prod_dvd_prod_of_dvd _ _ hsDiv
      simp only [Finset.prod_cons]
      rw [ih hsDiv, Nat.div_mul_div_comm haDiv hprodDiv]

/-- The exact-profile family has the same prescribed-mode word factor as
the full same-marginal family. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + 2 * beta + gamma + delta = N)
    (a : MME.StothersFourth.Phi224.ExactProfileWord
      N alpha beta gamma delta) (i : Fin 3) :
    Nat.card
        (MME.StothersFourth.Phi224.ExactProfileWord
          N alpha beta gamma delta) =
      ((2 * N).factorial /
        ∏ s : Fin 5,
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s).factorial) *
        Nat.card
          {b : MME.StothersFourth.Phi224.ExactProfileWord
              N alpha beta gamma delta //
            MME.StothersFourth.Phi224.modeWord b.1 i =
              MME.StothersFourth.Phi224.modeWord a.1 i} := by
  classical
  let k : Fin 9 → ℕ :=
    MME.StothersFourth.Phi224.profileMultiplicity
      alpha beta gamma delta
  let numerator : ℕ :=
    ∏ s : Fin 5,
      (MME.StothersFourth.Phi224.marginalMultiplicity
        alpha beta gamma delta i s).factorial
  let denominator : ℕ := ∏ r : Fin 9, (k r).factorial
  let wordCount : ℕ := (2 * N).factorial / numerator
  have hkMarginal : ∀ l : Fin 3, ∀ s : Fin 5,
      (∑ r : {r : Fin 9 //
          MME.StothersFourth.Phi224.pattern r l = s}, k r.1) =
        MME.StothersFourth.Phi224.marginalMultiplicity
          alpha beta gamma delta l s := by
    intro l s
    rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 9 ↦ MME.StothersFourth.Phi224.pattern r l) s k]
    fin_cases l <;> fin_cases s <;>
      simp [k, MME.StothersFourth.Phi224.pattern,
        MME.StothersFourth.Phi224.profileMultiplicity,
        MME.StothersFourth.Phi224.marginalMultiplicity,
        Fin.sum_univ_succ] <;> omega
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
        have hall :=
          (mme_stothers_phi224_exact_profile_marginals
            N alpha beta gamma delta hsum).2.2 a.1 a.2 i s
        exact hall.symm
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
  have hnumPos : 0 < numerator :=
    Finset.prod_pos fun s hs ↦ Nat.factorial_pos _
  have hrowDiv (s : Fin 5) :
      (∏ r : {r : Fin 9 //
          MME.StothersFourth.Phi224.pattern r i = s},
          (k r.1).factorial) ∣
        (MME.StothersFourth.Phi224.marginalMultiplicity
          alpha beta gamma delta i s).factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset
        {r : Fin 9 // MME.StothersFourth.Phi224.pattern r i = s})
      (fun r ↦ k r.1)
    simpa [hkMarginal i s] using h
  have hdenPartition :
      (∏ s : Fin 5,
        ∏ r : {r : Fin 9 //
            MME.StothersFourth.Phi224.pattern r i = s},
          (k r.1).factorial) = denominator := by
    calc
      (∏ s : Fin 5,
          ∏ r : {r : Fin 9 //
              MME.StothersFourth.Phi224.pattern r i = s},
            (k r.1).factorial) =
          ∏ x : Sigma fun s : Fin 5 ↦
            {r : Fin 9 // MME.StothersFourth.Phi224.pattern r i = s},
            (k x.2.1).factorial := by
        exact (Fintype.prod_sigma
          (fun x : Sigma fun s : Fin 5 ↦
            {r : Fin 9 // MME.StothersFourth.Phi224.pattern r i = s} ↦
            (k x.2.1).factorial)).symm
      _ = ∏ r : Fin 9, (k r).factorial := by
        simpa only using
          (Equiv.prod_comp
            (Equiv.sigmaFiberEquiv
              (fun r : Fin 9 ↦ MME.StothersFourth.Phi224.pattern r i))
            (fun r : Fin 9 ↦ (k r).factorial))
      _ = denominator := rfl
  have hdenDivNum : denominator ∣ numerator := by
    rw [← hdenPartition]
    exact Finset.prod_dvd_prod_of_dvd _ _ (by
      intro s hs
      exact hrowDiv s)
  let ExactStar :=
    {b : MME.StothersFourth.Phi224.ExactProfileWord
        N alpha beta gamma delta //
      MME.StothersFourth.Phi224.modeWord b.1 i =
        MME.StothersFourth.Phi224.modeWord a.1 i}
  have hstar : Nat.card ExactStar = numerator / denominator := by
    calc
      Nat.card ExactStar = ∏ s : Fin 5,
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s).factorial /
            ∏ r : {r : Fin 9 //
                MME.StothersFourth.Phi224.pattern r i = s},
              (k r.1).factorial := by
        simpa only [ExactStar, k] using
          (mme_stothers_phi224_fixed_mode_exact_profile_fiber_card
            N alpha beta gamma delta hsum a i)
      _ = numerator /
          ∏ s : Fin 5,
            ∏ r : {r : Fin 9 //
                MME.StothersFourth.Phi224.pattern r i = s},
              (k r.1).factorial := by
        exact prod_nat_div_eq_div_prod_of_dvd
          (Finset.univ : Finset (Fin 5))
          (fun s ↦
            (MME.StothersFourth.Phi224.marginalMultiplicity
              alpha beta gamma delta i s).factorial)
          (fun s ↦ ∏ r : {r : Fin 9 //
            MME.StothersFourth.Phi224.pattern r i = s},
            (k r.1).factorial)
          (by intro s hs; exact hrowDiv s)
      _ = numerator / denominator := by rw [hdenPartition]
  have htotal : Nat.card
      (MME.StothersFourth.Phi224.ExactProfileWord
        N alpha beta gamma delta) =
      (2 * N).factorial / denominator := by
    simpa only [denominator, k] using
      (mme_stothers_phi224_exact_profile_card
        N alpha beta gamma delta hsum)
  have hfactor : (2 * N).factorial / denominator =
      wordCount * (numerator / denominator) := by
    symm
    calc
      wordCount * (numerator / denominator) =
          ((2 * N).factorial / numerator) *
            (numerator / denominator) := by rfl
      _ = (2 * N).factorial * numerator /
          (numerator * denominator) :=
        Nat.div_mul_div_comm hnumDivFact hdenDivNum
      _ = numerator * (2 * N).factorial /
          (numerator * denominator) := by
        rw [Nat.mul_comm (2 * N).factorial numerator]
      _ = (2 * N).factorial / denominator :=
        Nat.mul_div_mul_left (2 * N).factorial denominator hnumPos
  simpa only [ExactStar, numerator, wordCount, htotal, hstar] using hfactor
