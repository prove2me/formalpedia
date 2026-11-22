-- Prove2me | solution 1 for Erdos390.WholePaper.roughSaiasIntervalFixedDivisorShiftBudget_sharp_le_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:48:52.420794+00:00
-- url     : https://prove2.me/submissions/5e55097b-67d8-49b3-9ff6-1039352166bf

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009

/- Source module: Erdos390.WholePaper.FixedModulusReducedResidueCount -/
section


/-!
# Fixed-modulus reduced-residue counts

This file proves the elementary `O_W(1)` input used in the rough selector
and in the tangent-list census.  A reduced-residue predicate is counted on
literal finite intervals by splitting the interval into complete periods
and one remainder.  Multiples of a number coprime to the fixed modulus are
then reindexed exactly by division.

There is no prime-number theorem, smooth-number estimate, or asymptotic
hypothesis in this module.  The final CRT-style error constant is the
explicit number `M + 1`, independent of the multiplier and the interval.
-/

namespace Erdos390.WholePaper

noncomputable section









/-! ## Exact periodic decomposition -/

















/-! ## Explicit fixed-period error -/







/-! ## Exact CRT reindexing and multiplier-independent error -/



/-- Integer quotient lengths differ from real division by less than one.
This is the only extra endpoint cost after the exact multiplication
reindexing. -/
theorem quotientIocLength_sub_realLengthDiv_abs_lt_one
    {D lo hi : ℕ} (hD : 0 < D) (hlohi : lo ≤ hi) :
    |(((hi / D - lo / D : ℕ) : ℝ)) -
        ((hi - lo : ℕ) : ℝ) / (D : ℝ)| < 1 := by
  have hquotient : lo / D ≤ hi / D := Nat.div_le_div_right hlohi
  have hDRealPos : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast hD
  have hDReal : (D : ℝ) ≠ 0 := hDRealPos.ne'
  have hhi := congrArg (fun z : ℕ ↦ (z : ℝ)) (Nat.mod_add_div hi D)
  have hlo := congrArg (fun z : ℕ ↦ (z : ℝ)) (Nat.mod_add_div lo D)
  simp only [Nat.cast_add, Nat.cast_mul] at hhi hlo
  have herror :
      (((hi / D - lo / D : ℕ) : ℝ)) -
          ((hi - lo : ℕ) : ℝ) / (D : ℝ) =
        ((lo % D : ℕ) : ℝ) / (D : ℝ) -
          ((hi % D : ℕ) : ℝ) / (D : ℝ) := by
    rw [Nat.cast_sub hquotient, Nat.cast_sub hlohi]
    field_simp [hDReal]
    nlinarith [hhi, hlo]
  have hloMod : ((lo % D : ℕ) : ℝ) / (D : ℝ) < 1 := by
    apply (div_lt_one hDRealPos).2
    exact_mod_cast Nat.mod_lt lo hD
  have hhiMod : ((hi % D : ℕ) : ℝ) / (D : ℝ) < 1 := by
    apply (div_lt_one hDRealPos).2
    exact_mod_cast Nat.mod_lt hi hD
  have hloModNonneg :
      0 ≤ ((lo % D : ℕ) : ℝ) / (D : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hDRealPos.le
  have hhiModNonneg :
      0 ≤ ((hi % D : ℕ) : ℝ) / (D : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hDRealPos.le
  rw [herror, abs_lt]
  constructor <;> linarith



/-! ## Paper-head specializations -/









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSignedFractionalAbel -/
section


/-!
# Signed fractional correction and finite Abel decomposition for the Saias defect

This file goes one level below
`RoughSaiasReverseNormalFormDefectInvLogSqBound`.  It never assumes a bound
for that defect.  Instead it keeps the quotient fractional correction with
its sign, separates the reverse defect into a continuous normal-form prime
sum and that signed correction, and applies the project's existing finite
theta Abel identity to the continuous prime sum.

The resulting quantitative theorem assumes only a cumulative theta-error
bound.  Its right side is the explicit endpoint-plus-variation ledger for the
Saias theta weight.  Thus the remaining inverse-log-square problem is a
deterministic estimate for the displayed signed Abel center, not a renamed
copy of the original defect bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-! ## One quotient: retain the fractional correction with its sign -/











/-! ## The reverse defect as continuous part plus signed correction -/







/-! ## Exact finite theta Abel identity -/

















/-! ## The floor/frac-paired natural theta weight -/



























/-! ## Quantitative theta transfer, without a defect-bound premise -/













/-! ## Closed fourth-power theta specialization -/



theorem roughSaiasThetaFourthPowerConstant_pos :
    0 < roughSaiasThetaFourthPowerConstant :=
  (Classical.choose_spec
    (FriableAsymptotic.exists_primeLogSumUpTo_error_bound (4 : ℝ))).1









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSharpFixedHeadIntervalShift -/
section


/-!
# Sharp fixed-head interval shifts

The endpointwise fixed-head estimate loses one logarithm because it takes
absolute values before subtracting the two endpoints of an interval.  This
file retains that subtraction.  The Dickman main terms are first compared
at the interval level; the two residual increments are then bounded by the
already-proved sharp Saias endpoint approximation.

No new analytic predicate is introduced.  In particular, the only
approximation used below is
`roughSaiasSharpEndpointApproximationUpToFive`.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## The interval-level Dickman cancellation -/









/-! ## Adding the two residual increments -/





/-! ## The closed inverse-log-square specialization -/



/-- The abstract interval budget with the concrete sharp endpoint rate is
bounded by the explicit inverse-log-square budget above. -/
theorem roughSaiasIntervalFixedDivisorShiftBudget_sharp_le
    {A B y d : ℕ}
    (hy : 2 ≤ y) (hd : 0 < d) (hAB : A ≤ B) :
    roughSaiasIntervalFixedDivisorShiftBudget
        (roughSaiasInvLogSqEndpointRate
          roughSaiasSharpDefectConstant) A B y d ≤
      roughSaiasSharpIntervalFixedDivisorBudget A B y d := by
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hC : 0 ≤ roughSaiasSharpDefectConstant := by
    unfold roughSaiasSharpDefectConstant
    have htheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
      roughSaiasThetaFourthPowerConstant_pos.le
    positivity
  have heta :
      0 ≤ roughSaiasInvLogSqEndpointRate
        roughSaiasSharpDefectConstant y := by
    unfold roughSaiasInvLogSqEndpointRate
    positivity
  have hqA :
      (((A / d : ℕ) : ℝ)) ≤ (A : ℝ) / (d : ℝ) :=
    Nat.cast_div_le
  have hqB :
      (((B / d : ℕ) : ℝ)) ≤ (B : ℝ) / (d : ℝ) :=
    Nat.cast_div_le
  have hqsum :
      (((A / d : ℕ) : ℝ) + ((B / d : ℕ) : ℝ)) ≤
        ((A : ℝ) + (B : ℝ)) / (d : ℝ) := by
    calc
      (((A / d : ℕ) : ℝ) + ((B / d : ℕ) : ℝ)) ≤
          (A : ℝ) / (d : ℝ) + (B : ℝ) / (d : ℝ) :=
        add_le_add hqA hqB
      _ = ((A : ℝ) + (B : ℝ)) / (d : ℝ) := by ring
  have hfloor :=
    quotientIocLength_sub_realLengthDiv_abs_lt_one hd hAB
  have hqgap :
      (((B / d - A / d : ℕ) : ℝ)) ≤
        ((B - A : ℕ) : ℝ) / (d : ℝ) + 1 := by
    rw [abs_lt] at hfloor
    linarith
  have hqendpoint :
      roughSaiasInvLogSqEndpointRate
          roughSaiasSharpDefectConstant y *
            (((A / d : ℕ) : ℝ) + ((B / d : ℕ) : ℝ)) ≤
        roughSaiasInvLogSqEndpointRate
          roughSaiasSharpDefectConstant y *
            (((A : ℝ) + (B : ℝ)) / (d : ℝ)) :=
    mul_le_mul_of_nonneg_left hqsum heta
  have hqlength :
      5 * ((B / d - A / d : ℕ) : ℝ) /
          Real.log (y : ℝ) ≤
        5 * (((B - A : ℕ) : ℝ) / (d : ℝ) + 1) /
          Real.log (y : ℝ) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hqgap (by norm_num)) hlogY.le
  have hsmallBudget :
      roughSaiasInvLogSqEndpointRate
          roughSaiasSharpDefectConstant y *
            (((A / d : ℕ) : ℝ) + ((B / d : ℕ) : ℝ)) +
        5 * ((B / d - A / d : ℕ) : ℝ) /
          Real.log (y : ℝ) ≤
      roughSaiasInvLogSqEndpointRate
          roughSaiasSharpDefectConstant y *
            (((A : ℝ) + (B : ℝ)) / (d : ℝ)) +
        5 * (((B - A : ℕ) : ℝ) / (d : ℝ) + 1) /
          Real.log (y : ℝ) :=
    add_le_add hqendpoint hqlength
  unfold roughSaiasIntervalFixedDivisorShiftBudget
    roughSaiasPairTransitionBudget
    roughSaiasSharpIntervalFixedDivisorBudget
  calc
    6 + ((B - A : ℕ) : ℝ) *
          (Real.log (d : ℝ) + 2) /
            ((d : ℝ) * Real.log (y : ℝ)) +
        (roughSaiasInvLogSqEndpointRate
            roughSaiasSharpDefectConstant y *
              (((A / d : ℕ) : ℝ) + ((B / d : ℕ) : ℝ)) +
          5 * ((B / d - A / d : ℕ) : ℝ) /
            Real.log (y : ℝ)) +
        (roughSaiasInvLogSqEndpointRate
            roughSaiasSharpDefectConstant y *
              ((A : ℝ) + (B : ℝ)) +
          5 * ((B - A : ℕ) : ℝ) /
            Real.log (y : ℝ)) / (d : ℝ) ≤
      6 + ((B - A : ℕ) : ℝ) *
          (Real.log (d : ℝ) + 2) /
            ((d : ℝ) * Real.log (y : ℝ)) +
        (roughSaiasInvLogSqEndpointRate
            roughSaiasSharpDefectConstant y *
              (((A : ℝ) + (B : ℝ)) / (d : ℝ)) +
          5 * (((B - A : ℕ) : ℝ) / (d : ℝ) + 1) /
            Real.log (y : ℝ)) +
        (roughSaiasInvLogSqEndpointRate
            roughSaiasSharpDefectConstant y *
              ((A : ℝ) + (B : ℝ)) +
          5 * ((B - A : ℕ) : ℝ) /
            Real.log (y : ℝ)) / (d : ℝ) := by
      exact add_le_add
        (add_le_add le_rfl hsmallBudget) le_rfl
    _ = 6 + 5 / Real.log (y : ℝ) +
        ((B - A : ℕ) : ℝ) *
          (Real.log (d : ℝ) + 12) /
            ((d : ℝ) * Real.log (y : ℝ)) +
        20 * roughSaiasSharpDefectConstant *
          ((A : ℝ) + (B : ℝ)) /
            ((d : ℝ) * Real.log (y : ℝ) ^ 2) := by
      unfold roughSaiasInvLogSqEndpointRate
      ring



/-! ## Physical blocks and the finite head -/

















end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_028 := by
  exact @Erdos390.WholePaper.roughSaiasIntervalFixedDivisorShiftBudget_sharp_le
