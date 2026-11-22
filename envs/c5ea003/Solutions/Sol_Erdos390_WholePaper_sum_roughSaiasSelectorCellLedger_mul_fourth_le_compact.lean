-- Prove2me | solution 1 for Erdos390.WholePaper.sum_roughSaiasSelectorCellLedger_mul_fourth_le_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:52:06.329781+00:00
-- url     : https://prove2.me/submissions/768fe5e0-4787-4a81-b175-e46e0642c80e

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



/-- First-moment Abel identity for the natural quotient drops.  Weighting
each drop by its base costs only the harmonic sum of the remaining
quotients; no individual jump is charged independently. -/
theorem sum_mul_roughSaiasNaturalQuotientDrop
    (X : ℕ) {M Z : ℕ} (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico M Z,
        (m : ℝ) * roughSaiasNaturalQuotientDrop X m) =
      (M : ℝ) * ((X / M : ℕ) : ℝ) -
        (Z : ℝ) * ((X / Z : ℕ) : ℝ) +
        ∑ m ∈ Finset.Ioc M Z, ((X / m : ℕ) : ℝ) := by
  induction Z, hMZ using Nat.le_induction with
  | base => simp
  | succ Z hMZ ih =>
      rw [Finset.sum_Ico_succ_top hMZ, ih,
        Finset.sum_Ioc_succ_top hMZ]
      unfold roughSaiasNaturalQuotientDrop
      push_cast
      ring

/-- Quantitative first-moment bound for quotient drops.  The right side is
the exact `X log Z` scale supplied by the hyperbola telescope. -/
theorem sum_mul_roughSaiasNaturalQuotientDrop_le
    (X : ℕ) {M Z : ℕ} (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico M Z,
        (m : ℝ) * roughSaiasNaturalQuotientDrop X m) ≤
      (X : ℝ) * (2 + Real.log (Z : ℝ)) := by
  have hMterm :
      (M : ℝ) * ((X / M : ℕ) : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast
      (show M * (X / M) ≤ X by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self X M)
  have hquotientSum :
      (∑ m ∈ Finset.Ioc M Z, ((X / m : ℕ) : ℝ)) ≤
        (X : ℝ) * ∑ m ∈ Finset.Ioc M Z, 1 / (m : ℝ) := by
    calc
      (∑ m ∈ Finset.Ioc M Z, ((X / m : ℕ) : ℝ)) ≤
          ∑ m ∈ Finset.Ioc M Z,
            (X : ℝ) * (1 / (m : ℝ)) := by
              apply Finset.sum_le_sum
              intro m _hm
              calc
                ((X / m : ℕ) : ℝ) ≤ (X : ℝ) / (m : ℝ) :=
                  Nat.cast_div_le
                _ = (X : ℝ) * (1 / (m : ℝ)) := by ring
      _ = (X : ℝ) * ∑ m ∈ Finset.Ioc M Z, 1 / (m : ℝ) := by
        rw [Finset.mul_sum]
  have hharmonic :
      (∑ m ∈ Finset.Ioc M Z, 1 / (m : ℝ)) ≤
        1 + Real.log (Z : ℝ) :=
    FriableAsymptotic.harmonic_Ioc_le
  rw [sum_mul_roughSaiasNaturalQuotientDrop X hMZ]
  calc
    (M : ℝ) * ((X / M : ℕ) : ℝ) -
          (Z : ℝ) * ((X / Z : ℕ) : ℝ) +
          ∑ m ∈ Finset.Ioc M Z, ((X / m : ℕ) : ℝ) ≤
        (M : ℝ) * ((X / M : ℕ) : ℝ) +
          ∑ m ∈ Finset.Ioc M Z, ((X / m : ℕ) : ℝ) := by
            have hnonneg :
                0 ≤ (Z : ℝ) * ((X / Z : ℕ) : ℝ) := by positivity
            linarith
    _ ≤ (X : ℝ) +
          (X : ℝ) * ∑ m ∈ Finset.Ioc M Z, 1 / (m : ℝ) :=
      add_le_add hMterm hquotientSum
    _ ≤ (X : ℝ) + (X : ℝ) * (1 + Real.log (Z : ℝ)) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hharmonic (by positivity))
    _ = (X : ℝ) * (2 + Real.log (Z : ℝ)) := by ring

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

/-- One reciprocal-log step costs at most
`1 / (m log(M)^2)` uniformly for `m ≥ M`. -/
theorem roughSaias_invLog_succ_sub_le
    {M m : ℕ} (hM2 : 2 ≤ M) (hMm : M ≤ m) :
    1 / Real.log (m : ℝ) -
        1 / Real.log ((m + 1 : ℕ) : ℝ) ≤
      1 / ((m : ℝ) * Real.log (M : ℝ) ^ 2) := by
  have hm2 : 2 ≤ m := hM2.trans hMm
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < M by omega)
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hm1pos : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogm1 : 0 < Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m + 1 by omega))
  have hlogMm : Real.log (M : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hMpos (by exact_mod_cast hMm)
  have hlogMm1 : Real.log (M : ℝ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) :=
    hlogMm.trans (Real.log_le_log hmpos (by exact_mod_cast (Nat.le_succ m)))
  have hgapNonneg :
      0 ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) :=
    sub_nonneg.mpr
      (Real.log_le_log hmpos (by exact_mod_cast (Nat.le_succ m)))
  have hgap :
      Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ≤
        1 / (m : ℝ) := by
    have hratio : 0 < ((m + 1 : ℕ) : ℝ) / (m : ℝ) :=
      div_pos hm1pos hmpos
    have h := Real.log_le_sub_one_of_pos hratio
    calc
      Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) =
          Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) := by
        rw [Real.log_div hm1pos.ne' hmpos.ne']
      _ ≤ ((m + 1 : ℕ) : ℝ) / (m : ℝ) - 1 := h
      _ = 1 / (m : ℝ) := by
        field_simp [hmpos.ne']
        norm_num
  have hdenom : Real.log (M : ℝ) ^ 2 ≤
      Real.log (m : ℝ) * Real.log ((m + 1 : ℕ) : ℝ) := by
    rw [pow_two]
    exact mul_le_mul hlogMm hlogMm1 hlogM.le hlogm.le
  have hinvIdentity :
      1 / Real.log (m : ℝ) -
          1 / Real.log ((m + 1 : ℕ) : ℝ) =
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) /
          (Real.log (m : ℝ) * Real.log ((m + 1 : ℕ) : ℝ)) := by
    field_simp [hlogm.ne', hlogm1.ne']
  rw [hinvIdentity]
  calc
    (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) /
          (Real.log (m : ℝ) * Real.log ((m + 1 : ℕ) : ℝ)) ≤
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) /
          Real.log (M : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left hgapNonneg (sq_pos_of_pos hlogM) hdenom
    _ ≤ (1 / (m : ℝ)) / Real.log (M : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hgap (sq_nonneg _)
    _ = 1 / ((m : ℝ) * Real.log (M : ℝ) ^ 2) := by ring

/-- A cell ledger is a telescoping quotient drop at the fixed left-hand
logarithm, plus an inverse-square summable tail. -/
theorem roughSaiasSelectorCellLedger_le_drop_add_invSq
    (X : ℕ) {M m : ℕ} (hM2 : 2 ≤ M) (hMm : M ≤ m) :
    roughSaiasSelectorCellLedger X m ≤
      roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ) +
        ((X : ℝ) / Real.log (M : ℝ) ^ 2) * (1 / (m : ℝ) ^ 2) := by
  have hm2 : 2 ≤ m := hM2.trans hMm
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogMm : Real.log (M : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast (show 0 < M by omega))
      (by exact_mod_cast hMm)
  have hdropNonneg : 0 ≤ roughSaiasNaturalQuotientDrop X m :=
    roughSaiasNaturalQuotientDrop_nonneg X (by omega)
  have hfirst :
      roughSaiasNaturalQuotientDrop X m / Real.log (m : ℝ) ≤
        roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ) :=
    div_le_div_of_nonneg_left hdropNonneg hlogM hlogMm
  have hinvNonneg := roughSaias_invLog_succ_sub_nonneg hm2
  have hinvBound := roughSaias_invLog_succ_sub_le hM2 hMm
  have hquotient : ((X / (m + 1) : ℕ) : ℝ) ≤
      (X : ℝ) / (m : ℝ) := by
    calc
      ((X / (m + 1) : ℕ) : ℝ) ≤
          (X : ℝ) / ((m + 1 : ℕ) : ℝ) := Nat.cast_div_le
      _ ≤ (X : ℝ) / (m : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hmpos
          (by exact_mod_cast (Nat.le_succ m))
  have hsecond :
      ((X / (m + 1) : ℕ) : ℝ) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) ≤
        ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
          (1 / (m : ℝ) ^ 2) := by
    calc
      ((X / (m + 1) : ℕ) : ℝ) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) ≤
        ((X : ℝ) / (m : ℝ)) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hquotient hinvNonneg
      _ ≤ ((X : ℝ) / (m : ℝ)) *
          (1 / ((m : ℝ) * Real.log (M : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hinvBound (by positivity)
      _ = ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
          (1 / (m : ℝ) ^ 2) := by ring
  unfold roughSaiasSelectorCellLedger
    roughSaiasNaturalQuotientDrop
  exact add_le_add hfirst hsecond









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























/-- Fourth-power PNT weighting of all upper selector ledgers.  The quotient
jump part uses the weighted hyperbola telescope, while the reciprocal-log
part uses only the harmonic bound. -/
theorem sum_roughSaiasSelectorCellLedger_mul_fourth_le
    {C : ℝ} (hC : 0 ≤ C) (X : ℕ) {M Z : ℕ}
    (hM2 : 2 ≤ M) (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico M Z,
        roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      C * (X : ℝ) * (2 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 5 +
        C * (X : ℝ) * (1 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 6 := by
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hpoint : ∀ m ∈ Finset.Ico M Z,
      roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) ≤
        (C / Real.log (M : ℝ) ^ 5) *
            ((m : ℝ) * roughSaiasNaturalQuotientDrop X m) +
          (C * (X : ℝ) / Real.log (M : ℝ) ^ 6) *
            (1 / (m : ℝ)) := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hm2 : 2 ≤ m := hM2.trans hmData.1
    have hmpos : 0 < (m : ℝ) := by positivity
    have hlogm : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    have hlogMm : Real.log (M : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log
        (by exact_mod_cast (show 0 < M by omega))
        (by exact_mod_cast hmData.1)
    have hpow4 : Real.log (M : ℝ) ^ 4 ≤
        Real.log (m : ℝ) ^ 4 :=
      pow_le_pow_left₀ hlogM.le hlogMm 4
    have hfactorNonneg :
        0 ≤ C * ((m : ℝ) / Real.log (m : ℝ) ^ 4) := by
      positivity
    have hfactorBound :
        C * ((m : ℝ) / Real.log (m : ℝ) ^ 4) ≤
          C * ((m : ℝ) / Real.log (M : ℝ) ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact div_le_div_of_nonneg_left (by positivity)
        (pow_pos hlogM 4) hpow4
    have hdrop : 0 ≤ roughSaiasNaturalQuotientDrop X m :=
      roughSaiasNaturalQuotientDrop_nonneg X (by omega)
    have hmajorantNonneg :
        0 ≤ roughSaiasNaturalQuotientDrop X m /
              Real.log (M : ℝ) +
            ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
              (1 / (m : ℝ) ^ 2) := by
      exact add_nonneg
        (div_nonneg hdrop hlogM.le)
        (mul_nonneg
          (div_nonneg (by positivity) (sq_nonneg _))
          (one_div_nonneg.mpr (sq_nonneg _)))
    calc
      roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) ≤
        (roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ) +
            ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
              (1 / (m : ℝ) ^ 2)) *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_right
          (roughSaiasSelectorCellLedger_le_drop_add_invSq
            X hM2 hmData.1) hfactorNonneg
      _ ≤
        (roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ) +
            ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
              (1 / (m : ℝ) ^ 2)) *
          (C * ((m : ℝ) / Real.log (M : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_left hfactorBound hmajorantNonneg
      _ = (C / Real.log (M : ℝ) ^ 5) *
            ((m : ℝ) * roughSaiasNaturalQuotientDrop X m) +
          (C * (X : ℝ) / Real.log (M : ℝ) ^ 6) *
            (1 / (m : ℝ)) := by
        field_simp [hlogM.ne', hmpos.ne']
  have hmoment := sum_mul_roughSaiasNaturalQuotientDrop_le X hMZ
  have hharmonicIco :
      (∑ m ∈ Finset.Ico M Z, 1 / (m : ℝ)) ≤
        1 + Real.log (Z : ℝ) := by
    calc
      (∑ m ∈ Finset.Ico M Z, 1 / (m : ℝ)) ≤
          ∑ m ∈ Finset.Ioc (M - 1) Z, 1 / (m : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          rw [Finset.mem_Ico] at hm
          rw [Finset.mem_Ioc]
          omega
        · intro m _hm _hnot
          positivity
      _ ≤ 1 + Real.log (Z : ℝ) :=
        FriableAsymptotic.harmonic_Ioc_le
  calc
    (∑ m ∈ Finset.Ico M Z,
        roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      ∑ m ∈ Finset.Ico M Z,
        ((C / Real.log (M : ℝ) ^ 5) *
            ((m : ℝ) * roughSaiasNaturalQuotientDrop X m) +
          (C * (X : ℝ) / Real.log (M : ℝ) ^ 6) *
            (1 / (m : ℝ))) :=
      Finset.sum_le_sum hpoint
    _ = (C / Real.log (M : ℝ) ^ 5) *
          (∑ m ∈ Finset.Ico M Z,
            (m : ℝ) * roughSaiasNaturalQuotientDrop X m) +
        (C * (X : ℝ) / Real.log (M : ℝ) ^ 6) *
          (∑ m ∈ Finset.Ico M Z, 1 / (m : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (C / Real.log (M : ℝ) ^ 5) *
          ((X : ℝ) * (2 + Real.log (Z : ℝ))) +
        (C * (X : ℝ) / Real.log (M : ℝ) ^ 6) *
          (1 + Real.log (Z : ℝ)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hmoment (by positivity))
        (mul_le_mul_of_nonneg_left hharmonicIco (by positivity))
    _ = C * (X : ℝ) * (2 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 5 +
        C * (X : ℝ) * (1 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 6 := by ring

































/-! ## Closed sharp defect and endpoint witnesses -/











end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_037 := by
  exact @Erdos390.WholePaper.sum_roughSaiasSelectorCellLedger_mul_fourth_le
