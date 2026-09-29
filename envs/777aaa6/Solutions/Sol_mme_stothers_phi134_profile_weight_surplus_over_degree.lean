-- Prove2me | solution 1 for mme_stothers_phi134_profile_weight_surplus_over_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:41:24.109679+00:00
-- url     : https://prove2.me/submissions/572c61bb-20fb-4969-9b21-b81b742472ac

import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_stothers_phi134_profile_data
import Theorems.Thm_mme_stothers_phi134_exact_profile_card
import Theorems.Thm_mme_stothers_phi134_capacity_identity
import Theorems.Thm_mme_stothers_phi134_capacity_entropy_lower_bound
import Theorems.Thm_mme_stothers_phi134_four_count_rounding
import Theorems.Thm_mme_stothers_phi134_analytic_profile_surplus

open MME Real BigOperators Filter
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option warningAsError true

/-- A finite exact Phi134 profile whose component weight beats the sharp
cyclic collision degree and the explicit prime--Behrend loss. -/
theorem solution
    (sigma a c L E H V : ℝ)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (hL : 0 < L) (hE : 0 < E) (hH : 0 < H)
    (hV : 0 ≤ V)
    (hVlt :
      V <
        8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c))) :
    ∃ N alpha beta gamma delta : ℕ,
      0 < N ∧ alpha + beta + gamma + delta = N ∧
      let D := fun t : Fin 3 ↦
        ∏ s : Fin 5,
          (marginalMultiplicity N alpha beta gamma delta t s).factorial /
            ∏ r : {r : Fin 8 // pattern r t = s},
              (profileMultiplicity alpha beta gamma delta r.1).factorial
      V ^ (2 * N) * (D 0 * (D 1 * D 2) : ℕ) *
          Real.exp (4000 * Real.sqrt ((12 * N + 1 : ℕ) : ℝ)) <
        (Nat.card (ExactProfileAddress N alpha beta gamma delta) : ℝ) ^
            (3 : ℕ) *
          (L ^ (2 * beta + 2 * gamma) *
            E ^ (2 * alpha + 2 * beta + 4 * delta) *
            H ^ (2 * gamma)) := by
  classical
  let Z : ℝ :=
    8 *
      ((L / sigma) ^ sigma *
        (E / (1 - sigma)) ^ (1 - sigma)) *
      ((1 / a) ^ a *
        ((H / 2) / c) ^ c *
        (E / (1 - a - c)) ^ (1 - a - c))
  let U : ℝ := (V + Z) / 2
  have hVU : V < U := by dsimp only [U, Z]; linarith
  have hU : 0 < U := lt_of_le_of_lt hV hVU
  have hUZ : U < Z := by dsimp only [U, Z]; linarith
  obtain ⟨A, B, C, D, hsum, hA, hB, hC, hD⟩ :=
    mme_stothers_phi134_four_count_rounding
      sigma a c ha hc hcs hsa
  let modeDegree := fun n : ℕ ↦ fun t : Fin 3 ↦
    ∏ s : Fin 5,
      (marginalMultiplicity n (A n) (B n) (C n) (D n) t s).factorial /
        ∏ r : {r : Fin 8 // pattern r t = s},
          (profileMultiplicity (A n) (B n) (C n) (D n) r.1).factorial
  let degree := fun n : ℕ ↦
    modeDegree n 0 * (modeDegree n 1 * modeDegree n 2)
  let targetCard := fun n : ℕ ↦
    Nat.card (ExactProfileAddress n (A n) (B n) (C n) (D n))
  have hprofileTotal (n : ℕ) :
      ∑ r : Fin 8,
          profileMultiplicity (A n) (B n) (C n) (D n) r = 2 * n := by
    have hnSum := hsum n
    simp [profileMultiplicity, Fin.sum_univ_succ]
    omega
  have htarget (n : ℕ) : 0 < targetCard n := by
    dsimp only [targetCard]
    rw [mme_stothers_phi134_exact_profile_card
      n (A n) (B n) (C n) (D n) (hsum n)]
    have hh := Nat.multinomial_pos Finset.univ
      (profileMultiplicity (A n) (B n) (C n) (D n))
    simpa only [Nat.multinomial, hprofileTotal n] using hh
  have hdegree (n : ℕ) (_hn : 0 < n) : 0 < degree n := by
    have hid := mme_stothers_phi134_capacity_identity
      n (A n) (B n) (C n) (D n) (hsum n)
    change
      (∏ i : Fin 3,
          Nat.multinomial Finset.univ
            (marginalMultiplicity n (A n) (B n) (C n) (D n) i)) *
          degree n = (targetCard n) ^ 3 at hid
    have hrhs : 0 < (targetCard n) ^ 3 := pow_pos (htarget n) 3
    have hproduct : 0 <
        (∏ i : Fin 3,
          Nat.multinomial Finset.univ
            (marginalMultiplicity n (A n) (B n) (C n) (D n) i)) *
          degree n := by
      rw [hid]
      exact hrhs
    exact (CanonicallyOrderedAdd.mul_pos.mp hproduct).2
  have hcapacity (n : ℕ) (hn : 0 < n) :
      Real.exp ((2 * n : ℝ) *
        (let an := (A n : ℝ) / n
         let cn := (C n : ℝ) / n
         let sn := ((B n : ℝ) + C n) / n
         (3 - cn) * Real.log 2 +
           Real.negMulLog sn + Real.negMulLog (1 - sn) +
           Real.negMulLog an + Real.negMulLog cn +
           Real.negMulLog (1 - an - cn))) ≤
        (6 * ((2 * n + 1 : ℕ) : ℝ)) ^ (15 : ℕ) *
          ((targetCard n : ℝ) ^ (3 : ℕ) / (degree n : ℝ)) := by
    simpa only [targetCard, degree, modeDegree] using
      (mme_stothers_phi134_capacity_entropy_lower_bound
        n (A n) (B n) (C n) (D n) hn (hsum n))
  obtain ⟨N, hN, hsumN, hsurplus⟩ :=
    mme_stothers_phi134_analytic_profile_surplus
      sigma a c L E H U A B C D degree targetCard
      ha hc hcs hsa hL hE hH hU hUZ hsum hA hB hC hD
      hdegree hcapacity
  refine ⟨N, A N, B N, C N, D N, hN, hsumN, ?_⟩
  dsimp only
  change
    V ^ (2 * N) * (degree N : ℝ) *
        Real.exp (4000 * Real.sqrt ((12 * N + 1 : ℕ) : ℝ)) <
      (targetCard N : ℝ) ^ (3 : ℕ) *
        (L ^ (2 * B N + 2 * C N) *
          E ^ (2 * A N + 2 * B N + 4 * D N) *
          H ^ (2 * C N))
  have hmono := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hV hVU.le (2 * N))
      (by positivity : (0 : ℝ) ≤ (degree N : ℝ)))
    (Real.exp_pos
      (4000 * Real.sqrt ((12 * N + 1 : ℕ) : ℝ))).le
  exact hmono.trans_lt hsurplus
