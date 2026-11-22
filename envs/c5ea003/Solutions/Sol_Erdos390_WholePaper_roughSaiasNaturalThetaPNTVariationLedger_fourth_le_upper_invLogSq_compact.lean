-- Prove2me | solution 1 for Erdos390.WholePaper.roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_invLogSq_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:51:27.8244+00:00
-- url     : https://prove2.me/submissions/fe3b8d2f-a74e-491a-b27f-bc3a8d3ee2f7

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
import Theorems.Thm_Erdos390_WholePaper_sum_roughSaiasSelectorCellLedger_mul_fourth_le_compact


section
theorem Erdos390.WholePaper.sum_roughSaiasSelectorCellLedger_mul_fourth_le : Erdos390.RemainingAnalyticGoal008_037 := @Erdos390.WholePaper.sum_roughSaiasSelectorCellLedger_mul_fourth_le_compact
end
/- Source module: Erdos390.WholePaper.RoughSaiasFullyRealBuchstabCells -/
section


/-!
# Unit-cell decomposition of the fully real Buchstab integral

The functional continuous-Buchstab identity is converted here into the
project's natural-base normal forms.  On a cell `s ∈ [m,m+1]`, the inner
term is split exactly into

* quotient drift at the current real base `s`, and
* real-base drift from `s` to the natural endpoint `m+1`.

No equality between the real and natural bases is left as a premise.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full

noncomputable section















/-! ## Natural unit cells -/

















/-- Pointwise right-endpoint quadrature bound for the quotient selector.
The first term is the exact natural quotient drop; hence its sum telescopes.
The second is only the variation of `1/log`. -/
theorem roughSaiasRealQuotientSelector_cell_sub_right_abs_le
    {X m : ℕ} (hm2 : 2 ≤ m) {s : ℝ}
    (hs : s ∈ Set.Icc (m : ℝ) (m + 1 : ℕ)) :
    |roughSaiasRealQuotientSelectorIntegrand X s -
        roughSaiasRealQuotientSelectorIntegrand X (m + 1 : ℕ)| ≤
      (((X / m : ℕ) : ℝ) - ((X / (m + 1) : ℕ) : ℝ)) /
          Real.log (m : ℝ) +
        ((X / (m + 1) : ℕ) : ℝ) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) := by
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hmpos : 0 < (m : ℝ) := zero_lt_one.trans hmone
  have hspos : 0 < s := hmpos.trans_le hs.1
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := by positivity
  have hrealLower :
      (X : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ (X : ℝ) / s :=
    div_le_div_of_nonneg_left hX0 hspos hs.2
  have hrealUpper :
      (X : ℝ) / s ≤ (X : ℝ) / (m : ℝ) :=
    div_le_div_of_nonneg_left hX0 hmpos hs.1
  have hfloorLower := Nat.floor_le_floor hrealLower
  have hfloorUpper := Nat.floor_le_floor hrealUpper
  rw [Nat.floor_div_eq_div] at hfloorLower hfloorUpper
  let A : ℝ := (((⌊(X : ℝ) / s⌋₊ : ℕ) : ℝ))
  let q₀ : ℝ := ((X / m : ℕ) : ℝ)
  let q₁ : ℝ := ((X / (m + 1) : ℕ) : ℝ)
  have hq₁A : q₁ ≤ A := by
    dsimp [q₁, A]
    exact_mod_cast hfloorLower
  have hAq₀ : A ≤ q₀ := by
    dsimp [A, q₀]
    exact_mod_cast hfloorUpper
  have hq₁0 : 0 ≤ q₁ := by positivity
  have hq₁q₀ : q₁ ≤ q₀ := hq₁A.trans hAq₀
  have hLm : 0 < Real.log (m : ℝ) := Real.log_pos hmone
  have hsone : 1 < s := hmone.trans_le hs.1
  have hLs : 0 < Real.log s := Real.log_pos hsone
  have hLmLs : Real.log (m : ℝ) ≤ Real.log s :=
    Real.log_le_log hmpos hs.1
  have hLsL1 : Real.log s ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_le_log hspos hs.2
  have hInvLmLs : 1 / Real.log s ≤ 1 / Real.log (m : ℝ) :=
    one_div_le_one_div_of_le hLm hLmLs
  have hselectorNonneg :
      0 ≤ A / Real.log s - q₁ / Real.log ((m + 1 : ℕ) : ℝ) := by
    have hleft : q₁ / Real.log ((m + 1 : ℕ) : ℝ) ≤
        q₁ / Real.log s :=
      div_le_div_of_nonneg_left hq₁0 hLs hLsL1
    have hright : q₁ / Real.log s ≤ A / Real.log s :=
      div_le_div_of_nonneg_right hq₁A hLs.le
    linarith
  have hfirst :
      (A - q₁) / Real.log s ≤
        (q₀ - q₁) / Real.log (m : ℝ) := by
    calc
      (A - q₁) / Real.log s ≤
          (q₀ - q₁) / Real.log s :=
        div_le_div_of_nonneg_right (sub_le_sub_right hAq₀ q₁) hLs.le
      _ ≤ (q₀ - q₁) / Real.log (m : ℝ) :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr hq₁q₀) hLm hLmLs
  have hsecond :
      q₁ * (1 / Real.log s -
          1 / Real.log ((m + 1 : ℕ) : ℝ)) ≤
        q₁ * (1 / Real.log (m : ℝ) -
          1 / Real.log ((m + 1 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left
      (sub_le_sub_right hInvLmLs _ ) hq₁0
  unfold roughSaiasRealQuotientSelectorIntegrand
  rw [Nat.floor_div_eq_div]
  change |A / Real.log s - q₁ / Real.log ((m + 1 : ℕ) : ℝ)| ≤ _
  rw [abs_of_nonneg hselectorNonneg]
  calc
    A / Real.log s - q₁ / Real.log ((m + 1 : ℕ) : ℝ) =
        (A - q₁) / Real.log s +
          q₁ * (1 / Real.log s -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) := by ring
    _ ≤ (q₀ - q₁) / Real.log (m : ℝ) +
        q₁ * (1 / Real.log (m : ℝ) -
          1 / Real.log ((m + 1 : ℕ) : ℝ)) :=
      add_le_add hfirst hsecond
    _ = (((X / m : ℕ) : ℝ) - ((X / (m + 1) : ℕ) : ℝ)) /
          Real.log (m : ℝ) +
        ((X / (m + 1) : ℕ) : ℝ) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) := by rfl



















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSelectorLedgerBound -/
section


/-!
# Summing the upper-cell quotient-selector ledger

On cells above the square-root transition the fully real Buchstab
integrand is the elementary quotient selector

`floor (X / s) / log s`.

The cell ledger from `RoughSaiasFullyRealBuchstabCells` has two pieces.
The natural quotient drops telescope exactly, while the reciprocal-log
variation is bounded by the convergent `sum 1 / m^2` tail.  This file makes
that summation quantitative without any asymptotic or defect premise.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section



theorem roughSaiasNaturalQuotientDrop_nonneg
    (X : ℕ) {m : ℕ} (hm : 0 < m) :
    0 ≤ roughSaiasNaturalQuotientDrop X m := by
  unfold roughSaiasNaturalQuotientDrop
  apply sub_nonneg.mpr
  exact_mod_cast Nat.div_le_div_left (a := X) (Nat.le_succ m) hm







theorem roughSaias_invLog_succ_sub_nonneg
    {m : ℕ} (hm2 : 2 ≤ m) :
    0 ≤ 1 / Real.log (m : ℝ) -
      1 / Real.log ((m + 1 : ℕ) : ℝ) := by
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogmono : Real.log (m : ℝ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast (show 0 < m by omega))
      (by exact_mod_cast (Nat.le_succ m))
  exact sub_nonneg.mpr (one_div_le_one_div_of_le hlogm hlogmono)













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasFullyRealNaturalCells -/
section


/-!
# Fully real cells with the floor/frac-paired natural endpoint sample

Sampling a fully real Buchstab cell by the continuous real-quotient theta
weight leaves a separate signed floor correction.  Sampling instead by the
natural quotient theta weight pairs that correction inside the cell.  The
sum of these paired cells is therefore exactly the natural integer Abel
consistency defect, with no signed-floor term left over.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section







/-- The paired natural endpoint sample is also the elementary quotient
selector on every upper cell. -/
theorem roughSaiasNaturalQuotientThetaWeight_eq_selector_of_sq_le
    {X m : ℕ} (hm2 : 2 ≤ m) (hupper : X ≤ m ^ 2) :
    roughSaiasNaturalQuotientThetaWeight X (m + 1) =
      roughSaiasRealQuotientSelectorIntegrand X (m + 1 : ℕ) := by
  have hmpos : 0 < m := by omega
  have hquotientLe : X / (m + 1) ≤ m := by
    calc
      X / (m + 1) ≤ X / m :=
        Nat.div_le_div_left (a := X) (Nat.le_succ m) hmpos
      _ ≤ m ^ 2 / m := Nat.div_le_div_right hupper
      _ = m := by
        simpa only [pow_two] using Nat.mul_div_left m hmpos
  unfold roughSaiasNaturalQuotientThetaWeight
    roughSaiasRealQuotientSelectorIntegrand
  rw [Nat.floor_div_eq_div]
  congr 1
  unfold roughSaiasNaturalMain
  by_cases hquotientZero : X / (m + 1) = 0
  · simp [hquotientZero]
  · have hquotientPos : 0 < X / (m + 1) := Nat.pos_of_ne_zero hquotientZero
    have hcoord := FriableAsymptotic.dickmanU_le_one hquotientPos
      (show 1 < m + 1 by omega) (hquotientLe.trans (Nat.le_succ m))
    rw [roughSaiasG_eq_one_of_le_one hcoord, mul_one]











end

end Erdos390.WholePaper

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

















/-- On the upper selector face, consecutive paired natural theta weights
are controlled by the already-summed selector cell ledger. -/
theorem roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_selectorCellLedger
    {X m : ℕ} (hm3 : 3 ≤ m) (hupper : X ≤ (m - 1) ^ 2) :
    |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
        roughSaiasNaturalQuotientThetaWeight X m| ≤
      roughSaiasSelectorCellLedger X m := by
  have hpred2 : 2 ≤ m - 1 := by omega
  have hpredSucc : m - 1 + 1 = m := by omega
  have hpredLe : m - 1 ≤ m := by omega
  have hupperNext : X ≤ m ^ 2 :=
    hupper.trans (Nat.pow_le_pow_left hpredLe 2)
  have hnow :=
    roughSaiasNaturalQuotientThetaWeight_eq_selector_of_sq_le
      (X := X) (m := m - 1) hpred2 hupper
  have hnext :=
    roughSaiasNaturalQuotientThetaWeight_eq_selector_of_sq_le
      (X := X) (m := m) (by omega) hupperNext
  rw [hpredSucc] at hnow
  have hcell := roughSaiasRealQuotientSelector_cell_sub_right_abs_le
    (X := X) (m := m) (by omega)
      (s := (m : ℝ)) (by constructor <;> norm_num)
  rw [hnext, hnow, abs_sub_comm]
  simpa only [roughSaiasSelectorCellLedger] using hcell













/-- On a range lying above the square-root transition, the complete
fourth-power natural-theta variation ledger is bounded by the explicit
hyperbola first moment and one harmonic tail. -/
theorem roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_explicit
    {C : ℝ} (hC : 0 ≤ C) {X M Z : ℕ}
    (hM2 : 2 ≤ M) (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ) C X M Z ≤
      C * (X : ℝ) * (2 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 5 +
        C * (X : ℝ) * (1 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 6 := by
  have hedgeSubset : Finset.Ioc M (Z - 1) ⊆ Finset.Ico M Z := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    rw [Finset.mem_Ico]
    omega
  have hpoint : ∀ m ∈ Finset.Ioc M (Z - 1),
      |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) ≤
        roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) := by
    intro m hm
    have hmData := Finset.mem_Ioc.mp hm
    have hMmPred : M ≤ m - 1 := by omega
    have hupperPred : X ≤ (m - 1) ^ 2 :=
      hupper.trans (Nat.pow_le_pow_left hMmPred 2)
    exact mul_le_mul_of_nonneg_right
      (roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_selectorCellLedger
        (by omega) hupperPred) (by positivity)
  have hnonneg : ∀ m ∈ Finset.Ico M Z,
      0 ≤ roughSaiasSelectorCellLedger X m *
        (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hm2 : 2 ≤ m := hM2.trans hmData.1
    have hlogm : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    have hdrop : 0 ≤ roughSaiasNaturalQuotientDrop X m :=
      roughSaiasNaturalQuotientDrop_nonneg X (by omega)
    have hledger : 0 ≤ roughSaiasSelectorCellLedger X m := by
      unfold roughSaiasSelectorCellLedger
      exact add_nonneg
        (div_nonneg hdrop hlogm.le)
        (mul_nonneg (by positivity)
          (roughSaias_invLog_succ_sub_nonneg hm2))
    exact mul_nonneg hledger (by positivity)
  unfold roughSaiasNaturalThetaPNTVariationLedger
  rw [← Nat.cast_ofNat (n := 4)]
  simp_rw [Real.rpow_natCast]
  calc
    (∑ m ∈ Finset.Ioc M (Z - 1),
        |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      ∑ m ∈ Finset.Ioc M (Z - 1),
        roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) :=
      Finset.sum_le_sum hpoint
    _ ≤ ∑ m ∈ Finset.Ico M Z,
        roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hedgeSubset
        (fun m hm _hnot ↦ hnonneg m hm)
    _ ≤ _ := sum_roughSaiasSelectorCellLedger_mul_fourth_le
      hC X hM2 hMZ

/-- The explicit upper-selector variation is already at the target
inverse-log-square scale. -/
theorem roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_invLogSq
    {C : ℝ} (hC : 0 ≤ C) {X M Z : ℕ}
    (hM3 : 3 ≤ M) (hMZ : M ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (M : ℝ) ≤ 5)
    (hupper : X ≤ M ^ 2) :
    roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ) C X M Z ≤
      13 * C * (X : ℝ) / Real.log (M : ℝ) ^ 2 := by
  have hMpos : 0 < (M : ℝ) := by positivity
  have hZpos : 0 < (Z : ℝ) := by
    exact_mod_cast (show 0 < Z by omega)
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hlogMOne : 1 ≤ Real.log (M : ℝ) := by
    have hexp : Real.exp 1 < (M : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast hM3)
    exact ((Real.lt_log_iff_exp_lt hMpos).2 hexp).le
  have hlogZX : Real.log (Z : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hZpos (by exact_mod_cast hZX)
  have hlogX : Real.log (X : ℝ) ≤ 5 * Real.log (M : ℝ) :=
    (div_le_iff₀ hlogM).mp hu5
  have hlogZ : Real.log (Z : ℝ) ≤ 5 * Real.log (M : ℝ) :=
    hlogZX.trans hlogX
  have hbracketTwo :
      2 + Real.log (Z : ℝ) ≤ 7 * Real.log (M : ℝ) := by
    linarith
  have hbracketOne :
      1 + Real.log (Z : ℝ) ≤ 6 * Real.log (M : ℝ) := by
    linarith
  have hCX : 0 ≤ C * (X : ℝ) := by positivity
  have hfirst :
      C * (X : ℝ) * (2 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 5 ≤
        7 * C * (X : ℝ) / Real.log (M : ℝ) ^ 4 := by
    calc
      C * (X : ℝ) * (2 + Real.log (Z : ℝ)) /
            Real.log (M : ℝ) ^ 5 ≤
          C * (X : ℝ) * (7 * Real.log (M : ℝ)) /
            Real.log (M : ℝ) ^ 5 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbracketTwo hCX)
          (pow_nonneg hlogM.le 5)
      _ = 7 * C * (X : ℝ) / Real.log (M : ℝ) ^ 4 := by
        field_simp [hlogM.ne']
  have hsecond :
      C * (X : ℝ) * (1 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 6 ≤
        6 * C * (X : ℝ) / Real.log (M : ℝ) ^ 5 := by
    calc
      C * (X : ℝ) * (1 + Real.log (Z : ℝ)) /
            Real.log (M : ℝ) ^ 6 ≤
          C * (X : ℝ) * (6 * Real.log (M : ℝ)) /
            Real.log (M : ℝ) ^ 6 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbracketOne hCX)
          (pow_nonneg hlogM.le 6)
      _ = 6 * C * (X : ℝ) / Real.log (M : ℝ) ^ 5 := by
        field_simp [hlogM.ne']
  have hpowTwoFour : Real.log (M : ℝ) ^ 2 ≤
      Real.log (M : ℝ) ^ 4 := by
    calc
      Real.log (M : ℝ) ^ 2 = Real.log (M : ℝ) ^ 2 * 1 := by ring
      _ ≤ Real.log (M : ℝ) ^ 2 * Real.log (M : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hlogMOne)
          (sq_nonneg _)
      _ = Real.log (M : ℝ) ^ 4 := by ring
  have hpowTwoFive : Real.log (M : ℝ) ^ 2 ≤
      Real.log (M : ℝ) ^ 5 := by
    calc
      Real.log (M : ℝ) ^ 2 = Real.log (M : ℝ) ^ 2 * 1 := by ring
      _ ≤ Real.log (M : ℝ) ^ 2 * Real.log (M : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hlogMOne)
          (sq_nonneg _)
      _ = Real.log (M : ℝ) ^ 5 := by ring
  have hfirstTarget :
      7 * C * (X : ℝ) / Real.log (M : ℝ) ^ 4 ≤
        7 * C * (X : ℝ) / Real.log (M : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity)
      (pow_pos hlogM 2) hpowTwoFour
  have hsecondTarget :
      6 * C * (X : ℝ) / Real.log (M : ℝ) ^ 5 ≤
        6 * C * (X : ℝ) / Real.log (M : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity)
      (pow_pos hlogM 2) hpowTwoFive
  calc
    roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ) C X M Z ≤
      C * (X : ℝ) * (2 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 5 +
      C * (X : ℝ) * (1 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 6 :=
      roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_explicit
        hC (by omega) hMZ hupper
    _ ≤ 7 * C * (X : ℝ) / Real.log (M : ℝ) ^ 4 +
        6 * C * (X : ℝ) / Real.log (M : ℝ) ^ 5 :=
      add_le_add hfirst hsecond
    _ ≤ 7 * C * (X : ℝ) / Real.log (M : ℝ) ^ 2 +
        6 * C * (X : ℝ) / Real.log (M : ℝ) ^ 2 :=
      add_le_add hfirstTarget hsecondTarget
    _ = 13 * C * (X : ℝ) / Real.log (M : ℝ) ^ 2 := by ring























/-! ## Closed sharp defect and endpoint witnesses -/











end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_031 := by
  exact @Erdos390.WholePaper.roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_invLogSq
