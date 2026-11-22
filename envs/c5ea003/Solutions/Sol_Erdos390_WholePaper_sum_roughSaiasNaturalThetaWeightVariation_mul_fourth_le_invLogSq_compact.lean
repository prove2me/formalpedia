-- Prove2me | solution 1 for Erdos390.WholePaper.sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_invLogSq_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:51:53.214567+00:00
-- url     : https://prove2.me/submissions/e7ba5c8e-c9da-4806-8048-1e911aa30e8d

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_008
import Theorems.Thm_Erdos390_WholePaper_sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_hyperbola_compact


section
theorem Erdos390.WholePaper.sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_hyperbola : Erdos390.RemainingAnalyticGoal008_035 := @Erdos390.WholePaper.sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_hyperbola_compact
end
/- Source module: Erdos390.WholePaper.RoughSaiasSharpCorrectionTarget -/
section


/-!
# The sharp fully real correction target

The reverse defect splits directly into:

1. the ordinary Dickman continuous-integral versus prime-theta
   discrepancy, already closed by the existing Riemann and fourth-power
   PNT estimates; and
2. one fully real Saias correction integral versus its matching residual
   prime weight.

This is the minimal analytic target left after all exact base changes,
floor pairings, upper-selector cells, and standard Dickman estimates have
been discharged.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section



































/-! ## Closing the lower fully-real quadrature -/



























/-- The arbitrary-face hyperbola variation is already at the target
inverse-log-square scale. -/
theorem sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_invLogSq
    {C : ℝ} (hC : 0 ≤ C) {X a b : ℕ}
    (ha3 : 3 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      211 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 := by
  have hapos : 0 < (a : ℝ) := by positivity
  have hbpos : 0 < (b : ℝ) := by
    exact_mod_cast (show 0 < b by omega)
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogaOne : 1 ≤ Real.log (a : ℝ) := by
    have hexp : Real.exp 1 < (a : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast ha3)
    exact ((Real.lt_log_iff_exp_lt hapos).2 hexp).le
  have hlogbX : Real.log (b : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hbpos (by exact_mod_cast hbX)
  have hlogX : Real.log (X : ℝ) ≤ 5 * Real.log (a : ℝ) :=
    (div_le_iff₀ hloga).mp hu5
  have hlogb : Real.log (b : ℝ) ≤ 5 * Real.log (a : ℝ) :=
    hlogbX.trans hlogX
  have hbracketTwo : 2 + Real.log (b : ℝ) ≤
      7 * Real.log (a : ℝ) := by linarith
  have hbracketOne : 1 + Real.log (b : ℝ) ≤
      6 * Real.log (a : ℝ) := by linarith
  have hCX : 0 ≤ C * (X : ℝ) := by positivity
  have hfirst :
      C * (X : ℝ) * (2 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 5 ≤
        7 * C * (X : ℝ) / Real.log (a : ℝ) ^ 4 := by
    calc
      C * (X : ℝ) * (2 + Real.log (b : ℝ)) /
            Real.log (a : ℝ) ^ 5 ≤
          C * (X : ℝ) * (7 * Real.log (a : ℝ)) /
            Real.log (a : ℝ) ^ 5 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbracketTwo hCX)
          (pow_nonneg hloga.le 5)
      _ = 7 * C * (X : ℝ) / Real.log (a : ℝ) ^ 4 := by
        field_simp [hloga.ne']
  have hsecond :
      C * (X : ℝ) * (1 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 6 ≤
        6 * C * (X : ℝ) / Real.log (a : ℝ) ^ 5 := by
    calc
      C * (X : ℝ) * (1 + Real.log (b : ℝ)) /
            Real.log (a : ℝ) ^ 6 ≤
          C * (X : ℝ) * (6 * Real.log (a : ℝ)) /
            Real.log (a : ℝ) ^ 6 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbracketOne hCX)
          (pow_nonneg hloga.le 6)
      _ = 6 * C * (X : ℝ) / Real.log (a : ℝ) ^ 5 := by
        field_simp [hloga.ne']
  have hpowTwoFour : Real.log (a : ℝ) ^ 2 ≤ Real.log (a : ℝ) ^ 4 := by
    calc
      Real.log (a : ℝ) ^ 2 = Real.log (a : ℝ) ^ 2 * 1 := by ring
      _ ≤ Real.log (a : ℝ) ^ 2 * Real.log (a : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hlogaOne) (sq_nonneg _)
      _ = Real.log (a : ℝ) ^ 4 := by ring
  have hpowTwoFive : Real.log (a : ℝ) ^ 2 ≤ Real.log (a : ℝ) ^ 5 := by
    calc
      Real.log (a : ℝ) ^ 2 = Real.log (a : ℝ) ^ 2 * 1 := by ring
      _ ≤ Real.log (a : ℝ) ^ 2 * Real.log (a : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hlogaOne) (sq_nonneg _)
      _ = Real.log (a : ℝ) ^ 5 := by ring
  have hfirstTarget :
      7 * C * (X : ℝ) / Real.log (a : ℝ) ^ 4 ≤
        7 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity)
      (pow_pos hloga 2) hpowTwoFour
  have hsecondTarget :
      6 * C * (X : ℝ) / Real.log (a : ℝ) ^ 5 ≤
        6 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity)
      (pow_pos hloga 2) hpowTwoFive
  have hinvLeOne : 1 / Real.log (a : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hlogaOne
  have hthirdBracket : 1 + 2 / Real.log (a : ℝ) ≤ 3 := by
    calc
      1 + 2 / Real.log (a : ℝ) =
          1 + 2 * (1 / Real.log (a : ℝ)) := by ring
      _ ≤ 1 + 2 * 1 :=
        add_le_add
          le_rfl
          (mul_le_mul_of_nonneg_left hinvLeOne
            (by norm_num : (0 : ℝ) ≤ 2))
      _ = 3 := by norm_num
  have hthirdCoeff :
      C * (X : ℝ) / Real.log (a : ℝ) ^ 5 ≤
        C * (X : ℝ) / Real.log (a : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left hCX (pow_pos hloga 2) hpowTwoFive
  have hthird :
      (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) *
          (1 + 2 / Real.log (a : ℝ)) ≤
        3 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 := by
    calc
      (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) *
          (1 + 2 / Real.log (a : ℝ)) ≤
        (C * (X : ℝ) / Real.log (a : ℝ) ^ 2) * 3 :=
          mul_le_mul hthirdCoeff hthirdBracket (by positivity) (by positivity)
      _ = 3 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 := by ring
  have hfull := sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_hyperbola
    hC (show 2 ≤ a by omega) hab hbX hu5
  calc
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      16 * (C * (X : ℝ) * (2 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 5 +
        C * (X : ℝ) * (1 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 6) +
        (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) *
          (1 + 2 / Real.log (a : ℝ)) := hfull
    _ ≤ 16 * (7 * C * (X : ℝ) / Real.log (a : ℝ) ^ 4 +
        6 * C * (X : ℝ) / Real.log (a : ℝ) ^ 5) +
        3 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num))
        hthird
    _ ≤ 16 * (7 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 +
        6 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2) +
        3 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (add_le_add hfirstTarget hsecondTarget)
          (by norm_num : (0 : ℝ) ≤ 16))
        le_rfl
    _ = 211 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 := by ring





























/-! ## Closed sharp defect and endpoint witnesses -/











end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_036 := by
  exact @Erdos390.WholePaper.sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_invLogSq
