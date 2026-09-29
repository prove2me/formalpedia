-- Prove2me | solution 1 for mme_stothers_phi125_finite_power_block_certificate_all_exponents
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T09:03:55.874737+00:00
-- url     : https://prove2.me/submissions/5911fb92-63a1-4431-a205-1fee6244c1ca

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi125_profile_data
import Definitions.Def_mme_tau_value
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic
import Theorems.Thm_mme_stothers_phi125_scalar_finite_power_block_certificate
import Theorems.Thm_mme_stothers_phi125_finite_power_block_certificate_no_upper_bound

open MME MME.StothersFourth BigOperators Filter
universe u
set_option autoImplicit false

noncomputable def phi125_analytic_rate (L E H a b : ℝ) : ℝ :=
  4 / H * ((L / a)^a * ((E * H) / (1-a))^(1-a)) *
    ((L / b)^b * ((2 * H) / (1-b))^(1-b))

theorem phi125_log_analytic_rate (L E H a b : ℝ)
    (hL : 0 < L) (hE : 0 < E) (hH : 0 < H)
    (ha : 0 < a) (hb : 0 < b) (ha1 : a < 1) (hb1 : b < 1) :
    Real.log (phi125_analytic_rate L E H a b) =
      Real.log 4 + (a+b)*Real.log L + (1-a)*Real.log E +
      (1-a-b)*Real.log H + (1-b)*Real.log 2 -
      a*Real.log a - (1-a)*Real.log (1-a) -
      b*Real.log b - (1-b)*Real.log (1-b) := by
  have ha' : 0 < 1-a := by linarith
  have hb' : 0 < 1-b := by linarith
  unfold phi125_analytic_rate
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_div (by norm_num) hH.ne',
    Real.log_rpow (by positivity), Real.log_rpow (by positivity),
    Real.log_rpow (by positivity), Real.log_rpow (by positivity)]
  rw [Real.log_div hL.ne' ha.ne', Real.log_div (by positivity) ha'.ne',
    Real.log_div hL.ne' hb.ne', Real.log_div (by positivity) hb'.ne',
    Real.log_mul hE.ne' hH.ne', Real.log_mul (by norm_num) hH.ne']
  ring

theorem phi125_analytic_rate_mono (L E H L' E' H' a b : ℝ)
    (hL : 0 < L) (hE : 0 < E) (hH : 0 < H)
    (hLL : L ≤ L') (hEE : E ≤ E') (hHH : H ≤ H')
    (ha : 0 < a) (hb : 0 < b) (hab : a+b ≤ 1) :
    phi125_analytic_rate L E H a b ≤ phi125_analytic_rate L' E' H' a b := by
  have hL' := hL.trans_le hLL
  have hE' := hE.trans_le hEE
  have hH' := hH.trans_le hHH
  have ha1 : a < 1 := by linarith
  have hb1 : b < 1 := by linarith
  have ha' : 0 < 1-a := by linarith
  have hb' : 0 < 1-b := by linarith
  have hp : 0 < phi125_analytic_rate L E H a b := by
    unfold phi125_analytic_rate
    positivity
  have hp' : 0 < phi125_analytic_rate L' E' H' a b := by
    unfold phi125_analytic_rate
    positivity
  apply (Real.log_le_log_iff hp hp').mp
  rw [phi125_log_analytic_rate L E H a b hL hE hH ha hb ha1 hb1,
    phi125_log_analytic_rate L' E' H' a b hL' hE' hH' ha hb ha1 hb1]
  have h1 := mul_le_mul_of_nonneg_left (Real.log_le_log hL hLL)
    (show 0 ≤ a+b by linarith)
  have h2 := mul_le_mul_of_nonneg_left (Real.log_le_log hE hEE)
    (show 0 ≤ 1-a by linarith)
  have h3 := mul_le_mul_of_nonneg_left (Real.log_le_log hH hHH)
    (show 0 ≤ 1-a-b by linarith)
  linarith


private theorem phi125_weighted_rate_le_add (X Y a : ℝ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (ha : 0 < a) (ha1 : a < 1) :
    (X/a)^a * (Y/(1-a))^(1-a) ≤ X+Y := by
  have ha' : 0 < 1-a := by linarith
  have h := Real.geom_mean_le_arith_mean2_weighted ha.le ha'.le
    (div_nonneg hX ha.le) (div_nonneg hY ha'.le) (by ring : a+(1-a)=1)
  convert h using 1
  field_simp

theorem phi125_scalar_analytic_upper (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a+b ≤ 1) :
    phi125_analytic_rate 5472 144 1444 a b ≤ 4942080 := by
  have ha1 : a < 1 := by linarith
  have hb1 : b < 1 := by linarith
  have hb' : 0 < 1-b := by linarith
  have hA := phi125_weighted_rate_le_add 5472 (144*1444) a
    (by norm_num) (by norm_num) ha ha1
  have hB := phi125_weighted_rate_le_add 5472 (2*1444) b
    (by norm_num) (by norm_num) hb hb1
  have h := mul_le_mul hA hB
    (by positivity) (by norm_num)
  have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4/1444)
  norm_num at hh
  norm_num [phi125_analytic_rate]
  simpa only [mul_assoc] using hh

theorem phi125_low_exponent_analytic_upper (tau a b : ℝ)
    (htau : 3*tau ≤ 2) (ha : 0 < a) (hb : 0 < b) (hab : a+b ≤ 1) :
    phi125_analytic_rate (L 6 tau) (E 6 tau) (H 6 tau) a b ≤ 4942080 := by
  have hE : E 6 tau ≤ 144 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 12) htau
    norm_num [E] at h ⊢
    exact h
  have hH : H 6 tau ≤ 1444 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 38) htau
    norm_num [H] at h ⊢
    exact h
  have hx := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6) htau
  norm_num at hx
  have hx0 := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6) (3*tau)
  have hL : L 6 tau ≤ 5472 := by
    norm_num [L]
    nlinarith
  exact (phi125_analytic_rate_mono _ _ _ 5472 144 1444 a b
    (by unfold L; positivity) (by unfold E; positivity) (by unfold H; positivity)
    hL hE hH ha hb hab).trans (phi125_scalar_analytic_upper a b ha hb hab)

theorem solution
    {K : Type u} [Field K] (tau a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V <
        4 / MME.StothersFourth.H 6 tau *
          ((MME.StothersFourth.L 6 tau / a) ^ a *
            ((MME.StothersFourth.E 6 tau *
              MME.StothersFourth.H 6 tau) / (1 - a)) ^ (1 - a)) *
          ((MME.StothersFourth.L 6 tau / b) ^ b *
            ((2 * MME.StothersFourth.H 6 tau) / (1 - b)) ^
              (1 - b))) :
    ∃ (N alpha beta gamma : ℕ),
      0 < N ∧ alpha + beta + gamma = N ∧
      ∃ (kept : Finset
          (MME.StothersFourth.Phi125.CyclicExactEdge
            N alpha beta gamma))
        (block : kept → TensorObj K 3) (B : ℝ),
        (∀ i : Fin 3,
          Function.Injective (fun e : kept ↦
            MME.StothersFourth.Phi125.cyclicModeWord e.1 i)) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j : Fin kept.card ↦
            block (kept.equivFin.symm j)))
          ((cyclicSymmetrization
            (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)).kronPow
              (2 * N)) ∧
        0 ≤ B ∧
        (∀ e : kept, ∀ W : ℝ,
          0 ≤ W → W < B → HasTauValueAtLeast (block e) tau W) ∧
        V ^ (2 * N) < (kept.card : ℝ) * B := by
  by_cases htau : 3*tau ≤ 2
  · apply mme_stothers_phi125_scalar_finite_power_block_certificate tau V hV
    exact hVlt.trans_le (phi125_low_exponent_analytic_upper tau a b htau ha hb hab)
  · exact mme_stothers_phi125_finite_power_block_certificate_no_upper_bound
      tau a b (by linarith) ha hb hab V hV hVlt

