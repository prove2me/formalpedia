-- Prove2me | solution 1 for Erdos390.WholePaper.roughCanonical_dickmanEndpointMain_sub_lower_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:42:05.356248+00:00
-- url     : https://prove2.me/submissions/b1010f78-807e-48ac-9fec-e10765158d09

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_007

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRawBroadSurplusAsymptotic -/
section


/-!
# Eventual raw broad-pool surplus on every active rough row

The tangent clean-list estimate is global in the common multiplier and
therefore cannot by itself give a lower bound in each complete rough row.
The rowwise input needed by the guard-capacity reduction is instead the
`active-clean-pool` estimate from Section 6 of the paper.  This file derives
that estimate from the already proved uniform de Bruijn bound and the
already proved fixed-head endpoint shift.

The proof has three quantitative layers.

* On a fixed-ratio interval `(A,B]`, the Dickman endpoint main term grows by
  a fixed positive multiple of `B-A`.  The uniform friable error is absorbed
  once `log y` is large.
* Exact head Möbius inversion and the fixed-divisor endpoint shift retain a
  fixed multiple of `A` in the head-free smooth interval.
* For an active label, `A = n / label` tends to infinity uniformly, while
  both `label / n` and `upperTailLength c n / n` tend to zero.  Consequently
  the broad pool dominates the literal upper-row quota and the three local
  guards.

The final theorem constructs
`RoughCanonicalActiveRawBroadSurplus ... 3 poolMinimum` for every fixed
`poolMinimum`, without a selector premise or an additional analytic
assumption.  The stronger linear real lower bound used to absorb that
constant is retained separately below.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells
open BankPaperRealization

noncomputable section

/-! ## A positive Dickman floor -/





/-- The value at the right endpoint `5` is a lower bound throughout the
compact Dickman range used by the rough rows. -/
theorem roughCanonicalPoolDickmanFloor_le_rho
    {u : Real} (_hu0 : 0 <= u) (hu5 : u <= 5) :
    roughCanonicalPoolDickmanFloor <= rho u := by
  unfold roughCanonicalPoolDickmanFloor
  by_cases hu1 : u <= 1
  · rw [rho_eq_one_of_le_one hu1]
    exact Erdos390.Full.FriableAsymptotic.rho_le_one_of_le_five le_rfl
  · have huMem : u ∈ Set.Icc (1 : Real) 5 :=
      ⟨le_of_not_ge hu1, hu5⟩
    have hfive : (5 : Real) ∈ Set.Icc (1 : Real) 5 := by norm_num
    exact antitoneOn_rho_one_five huMem hfive hu5

/-! ## Growth of the unrestricted smooth interval -/

/-- On the full compact de Bruijn range, the Dickman endpoint main term
grows by at least half the fixed Dickman floor once `log y` is large.

This elementary estimate uses the proved one-Lipschitz property of `rho`.
It deliberately keeps the natural endpoints `A,B`; all floor losses have
already occurred before this statement. -/
theorem roughCanonical_dickmanEndpointMain_sub_lower
    {A B y : Nat}
    (hyTwo : 2 <= y) (hA : 0 < A) (hAB : A <= B)
    (hlogB : Real.log (B : Real) <= 5 * Real.log (y : Real))
    (hlogLarge :
      2 / Real.log (y : Real) <= roughCanonicalPoolDickmanFloor) :
    roughCanonicalPoolDickmanFloor / 2 * ((B - A : Nat) : Real) <=
      (B : Real) * rho (FriableAsymptotic.dickmanU B y) -
        (A : Real) * rho (FriableAsymptotic.dickmanU A y) := by
  have hyReal : (1 : Real) < y := by exact_mod_cast (by omega : 1 < y)
  have hlogY : 0 < Real.log (y : Real) := Real.log_pos hyReal
  have hAReal : (0 : Real) < A := by exact_mod_cast hA
  have hBPos : 0 < B := hA.trans_le hAB
  have hBReal : (0 : Real) < B := by exact_mod_cast hBPos
  let uA : Real := Real.log (A : Real) / Real.log (y : Real)
  let uB : Real := Real.log (B : Real) / Real.log (y : Real)
  have hlogAB : Real.log (A : Real) <= Real.log (B : Real) :=
    Real.log_le_log hAReal (by exact_mod_cast hAB)
  have huAB : uA <= uB := by
    dsimp only [uA, uB]
    exact div_le_div_of_nonneg_right hlogAB hlogY.le
  have huA0 : 0 <= uA := by
    dsimp only [uA]
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 <= A by omega))) hlogY.le
  have huB0 : 0 <= uB := huA0.trans huAB
  have huB5 : uB <= 5 := by
    dsimp only [uB]
    exact (div_le_iff₀ hlogY).2 hlogB
  have hrhoFloor : roughCanonicalPoolDickmanFloor <= rho uB :=
    roughCanonicalPoolDickmanFloor_le_rho huB0 huB5
  have hrhoLip : |rho uB - rho uA| <= uB - uA := by
    exact FriableAsymptotic.rho_lipschitz_of_le_five huAB huB5
  have hrhoDiff : -(uB - uA) <= rho uB - rho uA :=
    (abs_le.mp hrhoLip).1
  have hlogGap :
      (A : Real) *
          (Real.log (B : Real) - Real.log (A : Real)) <=
        (B : Real) - (A : Real) := by
    have hratioPos : 0 < (B : Real) / (A : Real) :=
      div_pos hBReal hAReal
    have hlog := Real.log_le_sub_one_of_pos hratioPos
    rw [Real.log_div hBReal.ne' hAReal.ne'] at hlog
    have hscaled := mul_le_mul_of_nonneg_left hlog hAReal.le
    calc
      (A : Real) *
          (Real.log (B : Real) - Real.log (A : Real)) <=
        (A : Real) * ((B : Real) / (A : Real) - 1) := hscaled
      _ = (B : Real) - (A : Real) := by
        field_simp [hAReal.ne']
  have hcoordGap :
      (A : Real) * (uB - uA) <=
        ((B : Real) - (A : Real)) / Real.log (y : Real) := by
    calc
      (A : Real) * (uB - uA) =
          ((A : Real) *
              (Real.log (B : Real) - Real.log (A : Real))) /
            Real.log (y : Real) := by
        dsimp only [uA, uB]
        field_simp [hlogY.ne']
      _ <= ((B : Real) - (A : Real)) /
          Real.log (y : Real) :=
        div_le_div_of_nonneg_right hlogGap hlogY.le
  have hfloorHalf :
      roughCanonicalPoolDickmanFloor / 2 <=
        roughCanonicalPoolDickmanFloor -
          1 / Real.log (y : Real) := by
    have hinv : 2 * (1 / Real.log (y : Real)) <=
        roughCanonicalPoolDickmanFloor := by
      calc
        2 * (1 / Real.log (y : Real)) =
            2 / Real.log (y : Real) := by ring
        _ <= roughCanonicalPoolDickmanFloor := hlogLarge
    linarith
  have hlength : (0 : Real) <= (B : Real) - (A : Real) := by
    exact sub_nonneg.mpr (by exact_mod_cast hAB)
  have hcastSub : (((B - A : Nat) : Real)) =
      (B : Real) - (A : Real) := by
    rw [Nat.cast_sub hAB]
  rw [hcastSub]
  calc
    roughCanonicalPoolDickmanFloor / 2 *
          ((B : Real) - (A : Real)) <=
        (roughCanonicalPoolDickmanFloor -
            1 / Real.log (y : Real)) *
          ((B : Real) - (A : Real)) :=
      mul_le_mul_of_nonneg_right hfloorHalf hlength
    _ = roughCanonicalPoolDickmanFloor *
          ((B : Real) - (A : Real)) -
        ((B : Real) - (A : Real)) / Real.log (y : Real) := by ring
    _ <= ((B : Real) - (A : Real)) * rho uB -
        (A : Real) * (uB - uA) := by
      have hmainScaled :
          roughCanonicalPoolDickmanFloor *
              ((B : Real) - (A : Real)) <=
            ((B : Real) - (A : Real)) * rho uB := by
        calc
          _ = ((B : Real) - (A : Real)) *
              roughCanonicalPoolDickmanFloor := by ring
          _ <= ((B : Real) - (A : Real)) * rho uB :=
            mul_le_mul_of_nonneg_left hrhoFloor hlength
      exact sub_le_sub hmainScaled hcoordGap
    _ <= ((B : Real) - (A : Real)) * rho uB +
        (A : Real) * (rho uB - rho uA) := by
      have hmul := mul_le_mul_of_nonneg_left hrhoDiff hAReal.le
      linarith
    _ = (B : Real) * rho (FriableAsymptotic.dickmanU B y) -
        (A : Real) * rho (FriableAsymptotic.dickmanU A y) := by
      dsimp only [uA, uB, FriableAsymptotic.dickmanU]
      ring



/-! ## Closing the fixed head -/









/-! ## Literal rough-row adapters -/













/-! ## Uniform paper-scale choices -/























end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_017 := by
  exact @Erdos390.WholePaper.roughCanonical_dickmanEndpointMain_sub_lower
