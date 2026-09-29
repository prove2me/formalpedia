-- Prove2me | solution 1 for mme_stothers_q6_EHL_optimizer_regime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:07:59.830927+00:00
-- url     : https://prove2.me/submissions/0a6f2e76-1d8f-4eac-b3ed-1fd08e892b4d

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_stothers_fourth_data

open MME

set_option autoImplicit false

namespace MME.StothersFourth.RemainingFour

private theorem six_rpow_square (rho : ℝ) :
    (36 : ℝ) ^ rho = ((6 : ℝ) ^ rho) ^ (2 : ℕ) := by
  calc
    (36 : ℝ) ^ rho = (((6 : ℝ) ^ (2 : ℝ)) ^ rho) := by
      rw [Real.rpow_two]
      norm_num
    _ = (6 : ℝ) ^ ((2 : ℝ) * rho) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
    _ = (6 : ℝ) ^ (rho * (2 : ℝ)) := by ring_nf
    _ = (((6 : ℝ) ^ rho) ^ (2 : ℝ)) :=
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6) rho 2
    _ = ((6 : ℝ) ^ rho) ^ (2 : ℕ) := Real.rpow_two _

private theorem thirty_six_rpow_factor (rho : ℝ) :
    (38 : ℝ) ^ rho =
      (36 : ℝ) ^ rho * ((19 : ℝ) / 18) ^ rho := by
  rw [show (38 : ℝ) = 36 * (19 / 18) by norm_num]
  exact Real.mul_rpow (by norm_num) (by norm_num)

private theorem thirty_six_rpow_E_factor (rho : ℝ) :
    (36 : ℝ) ^ rho = (3 : ℝ) ^ rho * (12 : ℝ) ^ rho := by
  rw [show (36 : ℝ) = 3 * 12 by norm_num]
  exact Real.mul_rpow (by norm_num) (by norm_num)

/-- The complete analytic regime used by the four optimizer substitutions at
`q = 6`.  The final two inequalities are the exact `phi_224` feasibility
conditions after clearing positive denominators. -/
theorem q6_EHL_regime
    (tau : ℝ) (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    16 ≤ E 6 tau ∧
    E 6 tau < H 6 tau ∧
    H 6 tau < L 6 tau ∧
    L 6 tau < 4 * H 6 tau ∧
    (2 + E 6 tau) * L 6 tau ≤ 2 * H 6 tau * (E 6 tau + H 6 tau) ∧
    2 * E 6 tau * H 6 tau ≤ L 6 tau * (2 + E 6 tau + H 6 tau) := by
  let rho : ℝ := 3 * tau
  let A : ℝ := (6 : ℝ) ^ rho
  have hEnorm : E 6 tau = (12 : ℝ) ^ (3 * tau) := by norm_num [E]
  have hHnorm : H 6 tau = (38 : ℝ) ^ (3 * tau) := by norm_num [H]
  have hLnorm :
      L 6 tau = 4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2) := by
    norm_num [L]
  have hrho2 : 2 ≤ rho := by simpa [rho] using htauLower
  have hrho3 : rho ≤ 3 := by simpa [rho] using htauUpper
  have hrho0 : 0 ≤ rho := le_trans (by norm_num) hrho2
  have hrho1 : 1 ≤ rho := le_trans (by norm_num) hrho2
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hA36 : 36 ≤ A := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 6) hrho2
    norm_num [Real.rpow_two] at h
    simpa [A] using h
  have hEpos : 0 < E 6 tau := by
    unfold E
    positivity
  have hHpos : 0 < H 6 tau := by
    unfold H
    positivity
  have hLpos : 0 < L 6 tau := by
    unfold L
    positivity
  have hE16 : 16 ≤ E 6 tau := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 12) hrho2
    norm_num [Real.rpow_two] at h
    have h' : (144 : ℝ) ≤ (12 : ℝ) ^ rho := by simpa using h
    rw [hEnorm]
    simpa [rho] using (le_trans (by norm_num : (16 : ℝ) ≤ 144) h')
  have hEH : E 6 tau < H 6 tau := by
    rw [hEnorm, hHnorm]
    simpa [rho] using
      (Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 12)
        (by norm_num : (12 : ℝ) < 38)
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hrho2))
  have hHfactor : H 6 tau = A ^ (2 : ℕ) * ((19 : ℝ) / 18) ^ rho := by
    rw [hHnorm]
    change (38 : ℝ) ^ rho = A ^ (2 : ℕ) * ((19 : ℝ) / 18) ^ rho
    rw [thirty_six_rpow_factor, six_rpow_square]
  have hratioUpper : ((19 : ℝ) / 18) ^ rho < 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ (19 : ℝ) / 18) hrho3
    norm_num [Real.rpow_two] at h
    exact lt_of_le_of_lt h (by norm_num)
  have hH_lt_fourA2 : H 6 tau < 4 * A ^ (2 : ℕ) := by
    rw [hHfactor]
    calc
      A ^ (2 : ℕ) * ((19 : ℝ) / 18) ^ rho <
          A ^ (2 : ℕ) * 4 :=
        mul_lt_mul_of_pos_left hratioUpper (sq_pos_of_pos hApos)
      _ = 4 * A ^ (2 : ℕ) := by ring
  have hHL : H 6 tau < L 6 tau := by
    rw [hLnorm]
    change H 6 tau < 4 * A * (A + 2)
    nlinarith [sq_nonneg A]
  have hbern := one_add_mul_self_le_rpow_one_add
    (s := (1 : ℝ) / 18) (p := rho) (by norm_num) hrho1
  have hratioLower : (10 : ℝ) / 9 ≤ ((19 : ℝ) / 18) ^ rho := by
    norm_num at hbern ⊢
    nlinarith
  have hA2plus : A ^ (2 : ℕ) + 2 * A < H 6 tau := by
    rw [hHfactor]
    have hmul := mul_le_mul_of_nonneg_left hratioLower (sq_nonneg A)
    have hAlinear := mul_nonneg (sub_nonneg.mpr hA36) (le_of_lt hApos)
    nlinarith
  have hLH : L 6 tau < 4 * H 6 tau := by
    rw [hLnorm]
    change 4 * A * (A + 2) < 4 * H 6 tau
    nlinarith
  have h3pow9 : (9 : ℝ) ≤ (3 : ℝ) ^ rho := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hrho2
    norm_num [Real.rpow_two] at h
    exact h
  have h36le38 : (36 : ℝ) ^ rho ≤ (38 : ℝ) ^ rho :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) hrho0
  have hH9E : 9 * E 6 tau ≤ H 6 tau := by
    have h36le38' :
        (3 : ℝ) ^ rho * (12 : ℝ) ^ rho ≤ (38 : ℝ) ^ rho := by
      simpa [thirty_six_rpow_E_factor] using h36le38
    have hmul := mul_nonneg (sub_nonneg.mpr h3pow9)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 12) rho)
    have hineq : 9 * (12 : ℝ) ^ rho ≤ (38 : ℝ) ^ rho := by nlinarith
    rw [hEnorm, hHnorm]
    simpa [rho] using hineq
  have hH_E4 : E 6 tau + 4 ≤ H 6 tau := by
    nlinarith
  have h224left :
      (2 + E 6 tau) * L 6 tau ≤
        2 * H 6 tau * (E 6 tau + H 6 tau) := by
    have hp := mul_nonneg
      (sub_nonneg.mpr (le_of_lt hLH))
      (by positivity : 0 ≤ 2 + E 6 tau)
    have hq := mul_nonneg
      (le_of_lt hHpos)
      (sub_nonneg.mpr hH_E4)
    nlinarith
  have h224right :
      2 * E 6 tau * H 6 tau ≤
        L 6 tau * (2 + E 6 tau + H 6 tau) := by
    have hp := mul_nonneg
      (sub_nonneg.mpr (le_of_lt hHL))
      (by positivity : 0 ≤ 2 + E 6 tau + H 6 tau)
    have hq := mul_nonneg
      (le_of_lt hHpos)
      (by nlinarith [hEH] : 0 ≤ 2 + H 6 tau - E 6 tau)
    nlinarith
  exact ⟨hE16, hEH, hHL, hLH, h224left, h224right⟩

end MME.StothersFourth.RemainingFour

theorem solution
    (tau : ℝ) (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3) :
    16 ≤ MME.StothersFourth.E 6 tau ∧
    MME.StothersFourth.E 6 tau < MME.StothersFourth.H 6 tau ∧
    MME.StothersFourth.H 6 tau < MME.StothersFourth.L 6 tau ∧
    MME.StothersFourth.L 6 tau < 4 * MME.StothersFourth.H 6 tau ∧
    (2 + MME.StothersFourth.E 6 tau) * MME.StothersFourth.L 6 tau ≤
      2 * MME.StothersFourth.H 6 tau *
        (MME.StothersFourth.E 6 tau + MME.StothersFourth.H 6 tau) ∧
    2 * MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau ≤
      MME.StothersFourth.L 6 tau *
        (2 + MME.StothersFourth.E 6 tau + MME.StothersFourth.H 6 tau) := by
  exact MME.StothersFourth.RemainingFour.q6_EHL_regime tau htauLower htauUpper
