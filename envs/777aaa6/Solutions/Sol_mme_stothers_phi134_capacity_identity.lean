-- Prove2me | solution 1 for mme_stothers_phi134_capacity_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:41:36.593627+00:00
-- url     : https://prove2.me/submissions/424e893e-5d7f-4d82-b6bc-a6f1f8a51ae2

import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_stothers_phi134_profile_data
import Theorems.Thm_mme_stothers_phi134_exact_profile_card

open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true

namespace MME.StothersFourth.Phi134CapacitySubmission

private noncomputable def modeDegree
    (N alpha beta gamma delta : ℕ) (i : Fin 3) : ℕ :=
  ∏ s : Fin 5,
      (marginalMultiplicity N alpha beta gamma delta i s).factorial /
    ∏ r : {r : Fin 8 // pattern r i = s},
      (profileMultiplicity alpha beta gamma delta r.1).factorial

private noncomputable def degree
    (N alpha beta gamma delta : ℕ) : ℕ :=
  modeDegree N alpha beta gamma delta 0 *
    (modeDegree N alpha beta gamma delta 1 *
      modeDegree N alpha beta gamma delta 2)

private theorem count_totals
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    ∑ r : Fin 8, profileMultiplicity alpha beta gamma delta r = 2 * N := by
  simp [Fin.sum_univ_succ, profileMultiplicity]
  omega

private theorem marginal_totals
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) (i : Fin 3) :
    ∑ s : Fin 5, marginalMultiplicity N alpha beta gamma delta i s =
      2 * N := by
  fin_cases i <;>
    simp [Fin.sum_univ_succ, marginalMultiplicity] <;> omega

private theorem cell_counts
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N)
    (i : Fin 3) (s : Fin 5) :
    ∑ r : {r : Fin 8 // pattern r i = s},
        profileMultiplicity alpha beta gamma delta r.1 =
      marginalMultiplicity N alpha beta gamma delta i s := by
  classical
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun r : Fin 8 ↦ pattern r i = s))
    (by intro r; simp) (profileMultiplicity alpha beta gamma delta)]
  rw [Finset.sum_filter]
  fin_cases i <;> fin_cases s <;>
    norm_num [Fin.sum_univ_succ, Fin.reduceFinMk, Fin.succ,
      profileMultiplicity, marginalMultiplicity, pattern,
      MME.cwSquareBlockType] <;>
    norm_num [Fin.ext_iff] <;> omega

private theorem mode_factorization
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) (i : Fin 3) :
    Nat.card (ExactProfileAddress N alpha beta gamma delta) =
      ((2 * N).factorial /
        ∏ s : Fin 5,
          (marginalMultiplicity N alpha beta gamma delta i s).factorial) *
        modeDegree N alpha beta gamma delta i := by
  classical
  let J := ∏ r : Fin 8,
    (profileMultiplicity alpha beta gamma delta r).factorial
  let M := ∏ s : Fin 5,
    (marginalMultiplicity N alpha beta gamma delta i s).factorial
  have hc (s : Fin 5) :
      (∏ r : {r : Fin 8 // pattern r i = s},
          (profileMultiplicity alpha beta gamma delta r.1).factorial) *
        ((marginalMultiplicity N alpha beta gamma delta i s).factorial /
          ∏ r : {r : Fin 8 // pattern r i = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial) =
      (marginalMultiplicity N alpha beta gamma delta i s).factorial := by
    have hh := Nat.multinomial_spec Finset.univ
      (fun r : {r : Fin 8 // pattern r i = s} ↦
        profileMultiplicity alpha beta gamma delta r.1)
    simpa only [Nat.multinomial,
      cell_counts N alpha beta gamma delta hsum i s] using hh
  have hprod := congrArg (fun f : Fin 5 → ℕ ↦ ∏ s, f s) (funext hc)
  simp only [Finset.prod_mul_distrib] at hprod
  rw [Fintype.prod_fiberwise (fun r : Fin 8 ↦ pattern r i)
    (fun r ↦ (profileMultiplicity alpha beta gamma delta r).factorial)]
      at hprod
  change J * modeDegree N alpha beta gamma delta i = M at hprod
  have hrow := Nat.multinomial_spec Finset.univ
    (marginalMultiplicity N alpha beta gamma delta i)
  simp only [Nat.multinomial,
    marginal_totals N alpha beta gamma delta hsum i] at hrow
  have hjoint := Nat.multinomial_spec Finset.univ
    (profileMultiplicity alpha beta gamma delta)
  simp only [Nat.multinomial,
    count_totals N alpha beta gamma delta hsum] at hjoint
  rw [mme_stothers_phi134_exact_profile_card
    N alpha beta gamma delta hsum]
  have hJ : 0 < J :=
    Finset.prod_pos (fun _ _ ↦ Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_left hJ
  change J * ((2 * N).factorial / J) =
    J * (((2 * N).factorial / M) *
      modeDegree N alpha beta gamma delta i)
  calc
    _ = (2 * N).factorial := hjoint
    _ = M * ((2 * N).factorial / M) := hrow.symm
    _ = _ := by rw [← hprod]; ac_rfl

private theorem capacity_identity
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    (∏ i : Fin 3,
        Nat.multinomial Finset.univ
          (marginalMultiplicity N alpha beta gamma delta i)) *
        degree N alpha beta gamma delta =
      (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 := by
  have h0 := mode_factorization N alpha beta gamma delta hsum 0
  have h1 := mode_factorization N alpha beta gamma delta hsum 1
  have h2 := mode_factorization N alpha beta gamma delta hsum 2
  simp only [Nat.multinomial,
    marginal_totals N alpha beta gamma delta hsum]
  rw [Fin.prod_univ_three]
  unfold degree
  calc
    _ =
        (((2 * N).factorial /
            ∏ s : Fin 5,
              (marginalMultiplicity N alpha beta gamma delta 0 s).factorial) *
          modeDegree N alpha beta gamma delta 0) *
        (((2 * N).factorial /
            ∏ s : Fin 5,
              (marginalMultiplicity N alpha beta gamma delta 1 s).factorial) *
          modeDegree N alpha beta gamma delta 1) *
        (((2 * N).factorial /
            ∏ s : Fin 5,
              (marginalMultiplicity N alpha beta gamma delta 2 s).factorial) *
          modeDegree N alpha beta gamma delta 2) := by ring
    _ = _ := by rw [← h0, ← h1, ← h2]; ring

end MME.StothersFourth.Phi134CapacitySubmission

/-- Three marginal multinomials times the sharp cyclic collision degree
equal the cube of the exact-profile cardinality. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 // pattern r t = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial
    (∏ i : Fin 3,
        Nat.multinomial Finset.univ
          (marginalMultiplicity N alpha beta gamma delta i)) *
        (D 0 * (D 1 * D 2)) =
      (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 := by
  dsimp only
  simpa only [
    MME.StothersFourth.Phi134CapacitySubmission.degree,
    MME.StothersFourth.Phi134CapacitySubmission.modeDegree] using
    MME.StothersFourth.Phi134CapacitySubmission.capacity_identity
      N alpha beta gamma delta hsum
