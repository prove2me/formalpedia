-- Prove2me | solution 1 for mme_stothers_phi134_capacity_entropy_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:44:27.006698+00:00
-- url     : https://prove2.me/submissions/89eec03d-a9e0-4faa-a0c8-03c2dba8e64b

import Mathlib
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Definitions.Def_mme_stothers_phi134_profile_data
import Theorems.Thm_mme_stothers_phi134_exact_profile_card
import Theorems.Thm_mme_stothers_phi134_capacity_identity

open MME Real BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option warningAsError true

namespace MME.StothersFourth.Phi134CapacityEntropySubmission

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

private theorem multinomial_entropy
    (w : Fin 5 → ℕ) (n : ℕ) (hn : 0 < n)
    (hsum : ∑ i, w i = n) :
    Real.exp ((n : ℝ) *
        ∑ i, Real.negMulLog ((w i : ℝ) / n)) ≤
      (6 * ((n + 1 : ℕ) : ℝ)) ^ 5 *
        (Nat.multinomial Finset.univ w : ℝ) := by
  have h := mme_dwz_multinomial_entropy_polynomial_lower
    w 1 (by omega) (show 0 < ∑ i, w i by omega)
  have hlog : Real.log 2 ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  simp only [hsum, mul_one,
    mme_modern_entropyBits, Fintype.card_fin] at h
  have he (x : ℝ) :
      (n : ℝ) * Real.log 2 * (x / Real.log 2) = n * x := by
    field_simp
  rw [he] at h
  simpa only [Nat.cast_one, one_mul] using h

end MME.StothersFourth.Phi134CapacityEntropySubmission

open MME.StothersFourth.Phi134CapacityEntropySubmission

/-- Finite entropy capacity bound for the Phi134 profile. -/
theorem solution
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (hsum : alpha + beta + gamma + delta = N) :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (marginalMultiplicity N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 // pattern r t = s},
            (profileMultiplicity alpha beta gamma delta r.1).factorial
    let degreeValue := D 0 * (D 1 * D 2)
    Real.exp ((2 * N : ℝ) *
      (let an := (alpha : ℝ) / N
       let cn := (gamma : ℝ) / N
       let sn := ((beta : ℝ) + gamma) / N
       (3 - cn) * Real.log 2 +
         Real.negMulLog sn + Real.negMulLog (1 - sn) +
         Real.negMulLog an + Real.negMulLog cn +
         Real.negMulLog (1 - an - cn))) ≤
      (6 * ((2 * N + 1 : ℕ) : ℝ)) ^ (15 : ℕ) *
        ((Nat.card
          (ExactProfileAddress N alpha beta gamma delta) : ℝ) ^
            (3 : ℕ) /
          (degreeValue : ℝ)) := by
  dsimp only
  have hh (i : Fin 3) := multinomial_entropy
    (marginalMultiplicity N alpha beta gamma delta i)
    (2 * N) (by omega)
    (marginal_totals N alpha beta gamma delta hsum i)
  have hprod := Finset.prod_le_prod
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦
      (Real.exp_pos _).le)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) ↦ hh i)
  rw [← Real.exp_sum] at hprod
  simp only [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at hprod
  have hDnat : 0 < degree N alpha beta gamma delta := by
    have hid := mme_stothers_phi134_capacity_identity
      N alpha beta gamma delta hsum
    change
      (∏ i : Fin 3,
          Nat.multinomial Finset.univ
            (marginalMultiplicity N alpha beta gamma delta i)) *
          degree N alpha beta gamma delta =
        (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 at hid
    have hrows : 0 < ∏ i : Fin 3,
        Nat.multinomial Finset.univ
          (marginalMultiplicity N alpha beta gamma delta i) := by
      apply Finset.prod_pos
      intro i _hi
      exact Nat.multinomial_pos Finset.univ _
    have hcard : 0 < Nat.card
        (ExactProfileAddress N alpha beta gamma delta) := by
      rw [mme_stothers_phi134_exact_profile_card
        N alpha beta gamma delta hsum]
      have hm := Nat.multinomial_pos Finset.univ
        (profileMultiplicity alpha beta gamma delta)
      simpa only [Nat.multinomial,
        count_totals N alpha beta gamma delta hsum] using hm
    have hright : 0 <
        (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 :=
      pow_pos hcard _
    have hproduct : 0 <
        (∏ i : Fin 3,
          Nat.multinomial Finset.univ
            (marginalMultiplicity N alpha beta gamma delta i)) *
          degree N alpha beta gamma delta := by
      rw [hid]
      exact hright
    exact (CanonicallyOrderedAdd.mul_pos.mp hproduct).2
  have hD : (degree N alpha beta gamma delta : ℝ) ≠ 0 := by
    exact_mod_cast hDnat.ne'
  have hidNat := mme_stothers_phi134_capacity_identity
    N alpha beta gamma delta hsum
  change
    (∏ i : Fin 3,
        Nat.multinomial Finset.univ
          (marginalMultiplicity N alpha beta gamma delta i)) *
      degree N alpha beta gamma delta =
        (Nat.card (ExactProfileAddress N alpha beta gamma delta)) ^ 3 at hidNat
  have hid :
      (∏ i : Fin 3,
          (Nat.multinomial Finset.univ
            (marginalMultiplicity N alpha beta gamma delta i) : ℝ)) *
        (degree N alpha beta gamma delta : ℝ) =
      (Nat.card (ExactProfileAddress N alpha beta gamma delta) : ℝ) ^
        (3 : ℕ) := by
    exact_mod_cast hidNat
  have hratio :
      (∏ i : Fin 3,
          (Nat.multinomial Finset.univ
            (marginalMultiplicity N alpha beta gamma delta i) : ℝ)) =
        (Nat.card (ExactProfileAddress N alpha beta gamma delta) : ℝ) ^
            (3 : ℕ) /
          (degree N alpha beta gamma delta : ℝ) :=
    (eq_div_iff hD).mpr hid
  rw [hratio] at hprod
  have hn0 : (N : ℝ) ≠ 0 := by positivity
  have htwoN0 : (2 * (N : ℝ)) ≠ 0 := by positivity
  have hsumR :
      (alpha : ℝ) + beta + gamma + delta = N := by
    exact_mod_cast hsum
  have hhalf : (N : ℝ) / (2 * N) = 1 / 2 := by field_simp
  have henthalf : Real.negMulLog (1 / 2) = Real.log 2 / 2 := by
    norm_num [Real.negMulLog, Real.log_div]
    ring
  have hsplit (x : ℝ) :
      2 * Real.negMulLog (x / 2) =
        Real.negMulLog x + x * Real.log 2 := by
    rw [show x / 2 = x * (1 / 2 : ℝ) by ring,
      Real.negMulLog_mul, henthalf]
    ring
  have habgd :
      ((alpha : ℝ) + delta) / (2 * N) =
        (1 - (((beta : ℝ) + gamma) / N)) / 2 := by
    field_simp [hn0]
    nlinarith [hsumR]
  have hbg :
      ((beta : ℝ) + gamma) / (2 * N) =
        ((((beta : ℝ) + gamma) / N)) / 2 := by ring
  have ha : (alpha : ℝ) / (2 * N) =
      ((alpha : ℝ) / N) / 2 := by ring
  have hbd :
      ((beta : ℝ) + delta) / (2 * N) =
        (1 - (alpha : ℝ) / N - (gamma : ℝ) / N) / 2 := by
    field_simp [hn0]
    nlinarith [hsumR]
  have hc : (2 * gamma : ℝ) / (2 * N) =
      (gamma : ℝ) / N := by ring
  have hsumE :
      (∑ i : Fin 3, (2 * N : ℝ) *
        ∑ s : Fin 5,
          Real.negMulLog
            ((marginalMultiplicity N alpha beta gamma delta i s : ℝ) /
              (2 * N))) =
      (2 * N : ℝ) *
        (let an := (alpha : ℝ) / N
         let cn := (gamma : ℝ) / N
         let sn := ((beta : ℝ) + gamma) / N
         (3 - cn) * Real.log 2 +
           Real.negMulLog sn + Real.negMulLog (1 - sn) +
           Real.negMulLog an + Real.negMulLog cn +
           Real.negMulLog (1 - an - cn)) := by
    simp only [Fin.sum_univ_succ]
    norm_num [Fin.succ, marginalMultiplicity]
    rw [hhalf, habgd, hbg, ha, hbd, hc]
    rw [henthalf]
    calc
      _ = (2 * N : ℝ) *
          (Real.log 2 +
            2 * Real.negMulLog
              ((((beta : ℝ) + gamma) / N) / 2) +
            2 * Real.negMulLog
              ((1 - (((beta : ℝ) + gamma) / N)) / 2) +
            2 * Real.negMulLog (((alpha : ℝ) / N) / 2) +
            2 * Real.negMulLog
              ((1 - (alpha : ℝ) / N - (gamma : ℝ) / N) / 2) +
            Real.negMulLog ((gamma : ℝ) / N)) := by ring
      _ = _ := by
        rw [hsplit, hsplit, hsplit, hsplit]
        ring
  push_cast at hprod
  rw [hsumE] at hprod
  simpa only [← pow_mul, Nat.reduceMul, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one, degree, modeDegree] using hprod
