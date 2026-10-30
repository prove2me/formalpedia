-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.centralBinom_prob_sum_ge_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:31:57.286369+00:00
-- url     : https://prove2.me/submissions/2cb4d944-0bf6-449b-9516-bb84e41bfd9b

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_CentralBinomSum
import Mathlib.Data.Nat.Choose.Central
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Central-binomial Green sum: `√N ≤ ∑_{m<N} C_m / 4^m` (renewal route B, SRW Green helper)

The lazy/simple-random-walk Green local time over a horizon `N` is `∑_{m<N} a_m` with
`a_m = binom(2m,m)/4^m = Nat.centralBinom m / 4^m` the return probability.  The block-heat
lower bound `greenT_lower_fixed_window` consumes the fact that this partial sum grows like `√N`;
this file banks the clean, fully elementary lower bound

  `√N ≤ ∑_{m<N} Nat.centralBinom m / 4^m`,

with the *exact* constant `1`, via the term bound `1/√(4m+1) ≤ a_m` and the telescope
`√(m+1) − √m ≤ 1/√(4m+1)`.  No Stirling, Wallis, generating functions or integral estimates.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The multiplicative recurrence `a_{m+1} = a_m · (2m+1)/(2m+2)`. -/
lemma cbProb_succ (n : ℕ) :
    cbProb (n + 1) = cbProb n * ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) := by
  have h := Nat.succ_mul_centralBinom_succ n
  have hcast : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
      = 2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by exact_mod_cast h
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hcb : (Nat.centralBinom (n + 1) : ℝ)
      = 2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) / ((n : ℝ) + 1) := by
    rw [eq_div_iff hn1]; linear_combination hcast
  unfold cbProb
  rw [hcb, pow_succ]
  have hn2 : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  ring

/-- Square-comparison step: `1/√(4m+5) ≤ (2m+1)/(2m+2) · 1/√(4m+1)`. -/
lemma cbProb_ratio_step (m : ℕ) :
    1 / Real.sqrt (4 * (m : ℝ) + 5)
      ≤ ((2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2)) * (1 / Real.sqrt (4 * (m : ℝ) + 1)) := by
  have hA : (0 : ℝ) < 4 * (m : ℝ) + 1 := by positivity
  have hB : (0 : ℝ) < 4 * (m : ℝ) + 5 := by positivity
  have hden : (0 : ℝ) < 2 * (m : ℝ) + 2 := by positivity
  have hsqA : (0 : ℝ) < Real.sqrt (4 * (m : ℝ) + 1) := Real.sqrt_pos.mpr hA
  have hsqB : (0 : ℝ) < Real.sqrt (4 * (m : ℝ) + 5) := Real.sqrt_pos.mpr hB
  rw [div_mul_div_comm, mul_one,
    le_div_iff₀ (mul_pos hden hsqA), div_mul_eq_mul_div, div_le_iff₀ hsqB, one_mul]
  -- goal: (2m+2)·√(4m+1) ≤ (2m+1)·√(4m+5)
  have e1 : (2 * (m : ℝ) + 2) * Real.sqrt (4 * (m : ℝ) + 1)
      = Real.sqrt ((2 * (m : ℝ) + 2) ^ 2 * (4 * (m : ℝ) + 1)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have e2 : (2 * (m : ℝ) + 1) * Real.sqrt (4 * (m : ℝ) + 5)
      = Real.sqrt ((2 * (m : ℝ) + 1) ^ 2 * (4 * (m : ℝ) + 5)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [e1, e2]
  apply Real.sqrt_le_sqrt
  have hpoly : (2 * (m : ℝ) + 1) ^ 2 * (4 * (m : ℝ) + 5)
      - (2 * (m : ℝ) + 2) ^ 2 * (4 * (m : ℝ) + 1) = 1 := by ring
  linarith

/-- Term lower bound `1/√(4m+1) ≤ a_m`, by induction on the recurrence. -/
lemma inv_sqrt_four_mul_add_one_le_cbProb (m : ℕ) :
    1 / Real.sqrt (4 * (m : ℝ) + 1) ≤ cbProb m := by
  set_option backward.isDefEq.respectTransparency false in
    induction m with
    | zero => norm_num [cbProb, Nat.centralBinom_zero, Real.sqrt_one]
    | succ m ih =>
        have hcast5 : (4 * ((m + 1 : ℕ) : ℝ) + 1) = 4 * (m : ℝ) + 5 := by push_cast; ring
        rw [hcast5, cbProb_succ]
        calc 1 / Real.sqrt (4 * (m : ℝ) + 5)
            ≤ ((2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2)) * (1 / Real.sqrt (4 * (m : ℝ) + 1)) :=
              cbProb_ratio_step m
          _ ≤ ((2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2)) * cbProb m :=
              mul_le_mul_of_nonneg_left ih (by positivity)
          _ = cbProb m * ((2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2)) := by ring

/-- Telescoping term bound `√(m+1) − √m ≤ 1/√(4m+1)`. -/
lemma sqrt_succ_sub_le_inv_sqrt (m : ℕ) :
    Real.sqrt ((m : ℝ) + 1) - Real.sqrt (m : ℝ) ≤ 1 / Real.sqrt (4 * (m : ℝ) + 1) := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have h4 : (0 : ℝ) < 4 * (m : ℝ) + 1 := by positivity
  have hsum_pos : 0 < Real.sqrt ((m : ℝ) + 1) + Real.sqrt (m : ℝ) := by
    have : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have e1 : Real.sqrt ((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt hm1
  have e0 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hm
  have hdiff : Real.sqrt ((m : ℝ) + 1) - Real.sqrt (m : ℝ)
      = 1 / (Real.sqrt ((m : ℝ) + 1) + Real.sqrt (m : ℝ)) := by
    rw [eq_div_iff hsum_pos.ne']; nlinarith [e1, e0]
  have hden : Real.sqrt (4 * (m : ℝ) + 1)
      ≤ Real.sqrt ((m : ℝ) + 1) + Real.sqrt (m : ℝ) := by
    have hrhs_nonneg : 0 ≤ Real.sqrt ((m : ℝ) + 1) + Real.sqrt (m : ℝ) := hsum_pos.le
    rw [show Real.sqrt ((m : ℝ) + 1) + Real.sqrt (m : ℝ)
        = Real.sqrt ((Real.sqrt ((m : ℝ) + 1) + Real.sqrt (m : ℝ)) ^ 2) from
        (Real.sqrt_sq hrhs_nonneg).symm]
    apply Real.sqrt_le_sqrt
    have hcross : Real.sqrt ((m : ℝ) + 1) * Real.sqrt (m : ℝ)
        = Real.sqrt (((m : ℝ) + 1) * (m : ℝ)) := (Real.sqrt_mul hm1 _).symm
    have hge : (m : ℝ) ≤ Real.sqrt (((m : ℝ) + 1) * (m : ℝ)) := by
      have h1 : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1) * (m : ℝ) := by nlinarith [hm]
      calc (m : ℝ) = Real.sqrt ((m : ℝ) ^ 2) := (Real.sqrt_sq hm).symm
        _ ≤ Real.sqrt (((m : ℝ) + 1) * (m : ℝ)) := Real.sqrt_le_sqrt h1
    nlinarith [e1, e0, hcross, hge]
  rw [hdiff]
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr h4) hden

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Finset
theorem solution (N : ℕ) :
    Real.sqrt (N : ℝ) ≤ ∑ m ∈ Finset.range N, cbProb m := by
  have htel : ∑ m ∈ Finset.range N, (Real.sqrt ((m : ℝ) + 1) - Real.sqrt (m : ℝ))
      = Real.sqrt (N : ℝ) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [← htel]
  refine Finset.sum_le_sum (fun m _ => ?_)
  exact le_trans (sqrt_succ_sub_le_inv_sqrt m) (inv_sqrt_four_mul_add_one_le_cbProb m)
