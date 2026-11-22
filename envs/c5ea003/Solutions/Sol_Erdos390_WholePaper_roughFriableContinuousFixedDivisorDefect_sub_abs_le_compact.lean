-- Prove2me | solution 1 for Erdos390.WholePaper.roughFriableContinuousFixedDivisorDefect_sub_abs_le_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:44:59.331742+00:00
-- url     : https://prove2.me/submissions/6f0a42c9-42ee-47bc-a377-9dbe876f68c4

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_009

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





/-- The continuous fixed-divisor translation defects cancel on an
interval.  The term `log d` is the genuine fixed translation; the extra
`2` comes from comparing the two Dickman increments. -/
theorem roughFriableContinuousFixedDivisorDefect_sub_abs_le
    {A B y d : ℕ}
    (hy : 2 ≤ y) (hd : 0 < d) (hdA : d ≤ A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughFriableContinuousFixedDivisorDefect B y d -
        roughFriableContinuousFixedDivisorDefect A y d| ≤
      ((B - A : ℕ) : ℝ) *
        (Real.log (d : ℝ) + 2) /
          ((d : ℝ) * Real.log (y : ℝ)) := by
  have hA : 0 < A := hd.trans_le hdA
  have hB : 0 < B := hA.trans_le hAB
  have hAReal : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hBReal : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogd : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ d by omega))
  let uA : ℝ := FriableAsymptotic.dickmanU A y
  let uB : ℝ := FriableAsymptotic.dickmanU B y
  let t : ℝ := Real.log (d : ℝ) / Real.log (y : ℝ)
  have ht : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg hlogd hlogY.le
  have hlogAB : Real.log (A : ℝ) ≤ Real.log (B : ℝ) :=
    Real.log_le_log hAReal (by exact_mod_cast hAB)
  have huAB : uA ≤ uB := by
    dsimp [uA, uB, FriableAsymptotic.dickmanU]
    exact div_le_div_of_nonneg_right hlogAB hlogY.le
  have huB5 : uB ≤ 5 := by
    dsimp [uB, FriableAsymptotic.dickmanU]
    exact (div_le_iff₀ hlogY).2 hlogB
  have hshiftAB : uA - t ≤ uB - t := sub_le_sub_right huAB t
  have hshiftB5 : uB - t ≤ 5 :=
    (sub_le_self uB ht).trans huB5
  have hgB :
      |rho (uB - t) - rho uB| ≤ t := by
    rw [abs_sub_comm]
    calc
      |rho uB - rho (uB - t)| ≤ uB - (uB - t) :=
        FriableAsymptotic.rho_lipschitz_of_le_five
          (sub_le_self uB ht) huB5
      _ = t := by ring
  have hshiftRho :
      |rho (uB - t) - rho (uA - t)| ≤ uB - uA := by
    calc
      |rho (uB - t) - rho (uA - t)| ≤
          (uB - t) - (uA - t) :=
        FriableAsymptotic.rho_lipschitz_of_le_five
          hshiftAB hshiftB5
      _ = uB - uA := by ring
  have hunshiftRho :
      |rho uB - rho uA| ≤ uB - uA :=
    FriableAsymptotic.rho_lipschitz_of_le_five huAB huB5
  have hgDiff :
      |(rho (uB - t) - rho uB) -
          (rho (uA - t) - rho uA)| ≤
        2 * (uB - uA) := by
    calc
      |(rho (uB - t) - rho uB) -
          (rho (uA - t) - rho uA)| =
        |(rho (uB - t) - rho (uA - t)) -
          (rho uB - rho uA)| := by
            congr 1
            ring
      _ ≤ |rho (uB - t) - rho (uA - t)| +
          |rho uB - rho uA| := abs_sub _ _
      _ ≤ (uB - uA) + (uB - uA) :=
        add_le_add hshiftRho hunshiftRho
      _ = 2 * (uB - uA) := by ring
  have hlogQuotient :
      Real.log (B : ℝ) - Real.log (A : ℝ) ≤
        (B : ℝ) / (A : ℝ) - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hBReal hAReal)
    rw [Real.log_div hBReal.ne' hAReal.ne'] at h
    exact h
  have hscaledLog :
      (A : ℝ) *
          (Real.log (B : ℝ) - Real.log (A : ℝ)) ≤
        (B : ℝ) - (A : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlogQuotient hAReal.le
    calc
      (A : ℝ) *
          (Real.log (B : ℝ) - Real.log (A : ℝ)) ≤
        (A : ℝ) * ((B : ℝ) / (A : ℝ) - 1) := h
      _ = (B : ℝ) - (A : ℝ) := by field_simp
  have hAuDiff :
      (A : ℝ) * (uB - uA) ≤
        ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
    calc
      (A : ℝ) * (uB - uA) =
          (A : ℝ) *
            (Real.log (B : ℝ) - Real.log (A : ℝ)) /
              Real.log (y : ℝ) := by
                dsimp [uA, uB, FriableAsymptotic.dickmanU]
                ring
      _ ≤ ((B : ℝ) - (A : ℝ)) / Real.log (y : ℝ) :=
        div_le_div_of_nonneg_right hscaledLog hlogY.le
      _ = ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
        rw [Nat.cast_sub hAB]
  have hgapNonneg : 0 ≤ ((B - A : ℕ) : ℝ) / (d : ℝ) := by
    positivity
  have hfirst :
      |(((B - A : ℕ) : ℝ) / (d : ℝ)) *
          (rho (uB - t) - rho uB)| ≤
        (((B - A : ℕ) : ℝ) / (d : ℝ)) * t := by
    rw [abs_mul, abs_of_nonneg hgapNonneg]
    exact mul_le_mul_of_nonneg_left hgB hgapNonneg
  have hsecond :
      |((A : ℝ) / (d : ℝ)) *
          ((rho (uB - t) - rho uB) -
            (rho (uA - t) - rho uA))| ≤
        2 * ((B - A : ℕ) : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) := by
    rw [abs_mul, abs_of_pos (div_pos hAReal hdReal)]
    calc
      (A : ℝ) / (d : ℝ) *
          |(rho (uB - t) - rho uB) -
            (rho (uA - t) - rho uA)| ≤
        (A : ℝ) / (d : ℝ) * (2 * (uB - uA)) :=
          mul_le_mul_of_nonneg_left hgDiff
            (div_nonneg hAReal.le hdReal.le)
      _ = (2 / (d : ℝ)) * ((A : ℝ) * (uB - uA)) := by ring
      _ ≤ (2 / (d : ℝ)) *
          (((B - A : ℕ) : ℝ) / Real.log (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hAuDiff (by positivity)
      _ = 2 * ((B - A : ℕ) : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) := by ring
  change
    |(B : ℝ) / (d : ℝ) * (rho (uB - t) - rho uB) -
        (A : ℝ) / (d : ℝ) * (rho (uA - t) - rho uA)| ≤ _
  calc
    |(B : ℝ) / (d : ℝ) * (rho (uB - t) - rho uB) -
        (A : ℝ) / (d : ℝ) * (rho (uA - t) - rho uA)| =
      |(((B - A : ℕ) : ℝ) / (d : ℝ)) *
          (rho (uB - t) - rho uB) +
        ((A : ℝ) / (d : ℝ)) *
          ((rho (uB - t) - rho uB) -
            (rho (uA - t) - rho uA))| := by
              rw [Nat.cast_sub hAB]
              congr 1
              ring
    _ ≤
        |(((B - A : ℕ) : ℝ) / (d : ℝ)) *
          (rho (uB - t) - rho uB)| +
        |((A : ℝ) / (d : ℝ)) *
          ((rho (uB - t) - rho uB) -
            (rho (uA - t) - rho uA))| := abs_add_le _ _
    _ ≤ (((B - A : ℕ) : ℝ) / (d : ℝ)) * t +
        2 * ((B - A : ℕ) : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) :=
      add_le_add hfirst hsecond
    _ = ((B - A : ℕ) : ℝ) *
        (Real.log (d : ℝ) + 2) /
          ((d : ℝ) * Real.log (y : ℝ)) := by
      dsimp [t]
      ring



/-! ## Adding the two residual increments -/





/-! ## The closed inverse-log-square specialization -/







/-! ## Physical blocks and the finite head -/

















end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_020 := by
  exact @Erdos390.WholePaper.roughFriableContinuousFixedDivisorDefect_sub_abs_le
