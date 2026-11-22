-- Prove2me | solution 1 for Erdos390.WholePaper.roughFriableMain_abs_le_with_balanceError_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:46:41.056811+00:00
-- url     : https://prove2.me/submissions/e8e27808-890e-458d-aaab-81b23917504a

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

/- Source module: Erdos390.WholePaper.RoughBalancedFriableResidualReduction -/
section


/-!
# Residual cancellation in the balanced four-endpoint friable block

The closed de Bruijn theorem controls the endpoint residual

`R(X,y) = Psi(X,y) - X * rho(log X / log y)`

by `O(X / log y)`.  Applying that estimate independently at four
endpoints loses one logarithm.  This file avoids that lossy triangle
inequality.  It proves that the literal four-endpoint residual is exactly
two *short residual increments* plus one broad increment whose coefficient
already contains `1/L`.

It also records the exact reverse Buchstab recurrence for `R`, using one
common prime interval for both endpoints.  The remaining missing analytic
input is thereby reduced to a local regularity inequality for `R`; it is
strictly an estimate for the genuine friable counting function and contains
no selector, row, rounding, or feasibility conclusion.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The genuine endpoint residual -/















/-! ## Exact reverse Buchstab recurrence for the residual -/













/-! ## Verified regularity of the Dickman main term -/

/-- Symmetric compact one-Lipschitz control of the already constructed
Dickman function. -/
theorem roughRho_abs_sub_le_abs_of_le_five
    {a b : ℝ} (ha5 : a ≤ 5) (hb5 : b ≤ 5) :
    |rho a - rho b| ≤ |a - b| := by
  by_cases hab : a ≤ b
  · have h := FriableAsymptotic.rho_lipschitz_of_le_five hab hb5
    rw [abs_sub_comm (rho a), abs_sub_comm a]
    exact h.trans_eq (abs_of_nonneg (sub_nonneg.mpr hab)).symm
  · have hba : b ≤ a := le_of_not_ge hab
    have h := FriableAsymptotic.rho_lipschitz_of_le_five hba ha5
    exact h.trans_eq (abs_of_nonneg (sub_nonneg.mpr hba)).symm



/-- Floor endpoints need not retain the real first-moment balance exactly.
The same centering argument keeps the complete imbalance as one explicit
endpoint term.  On the positive compact Dickman range its coefficient has
absolute value at most one. -/
theorem roughFriableMain_abs_le_with_balanceError
    {ι : Type*} (I : Finset ι)
    (coeff : ι → ℝ) (endpoint : ι → ℕ) (base y : ℕ)
    (hendpoint5 : ∀ i ∈ I,
      FriableAsymptotic.dickmanU (endpoint i) y ≤ 5)
    (hbase0 : 0 ≤ FriableAsymptotic.dickmanU base y)
    (hbase5 : FriableAsymptotic.dickmanU base y ≤ 5) :
    |∑ i ∈ I,
        coeff i * roughFriableDickmanMain (endpoint i) y| ≤
      (∑ i ∈ I,
        |coeff i| * (endpoint i : ℝ) *
          |FriableAsymptotic.dickmanU (endpoint i) y -
            FriableAsymptotic.dickmanU base y|) +
      |∑ i ∈ I, coeff i * (endpoint i : ℝ)| := by
  have hcenter :
      (∑ i ∈ I,
          coeff i * roughFriableDickmanMain (endpoint i) y) =
        (∑ i ∈ I,
          coeff i * (endpoint i : ℝ) *
            (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
              rho (FriableAsymptotic.dickmanU base y))) +
        rho (FriableAsymptotic.dickmanU base y) *
          ∑ i ∈ I, coeff i * (endpoint i : ℝ) := by
    unfold roughFriableDickmanMain
    calc
      ∑ i ∈ I,
          coeff i *
            ((endpoint i : ℝ) *
              rho (FriableAsymptotic.dickmanU (endpoint i) y)) =
        ∑ i ∈ I,
          (coeff i * (endpoint i : ℝ) *
              (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
                rho (FriableAsymptotic.dickmanU base y)) +
            rho (FriableAsymptotic.dickmanU base y) *
              (coeff i * (endpoint i : ℝ))) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hcenterBound :
      |∑ i ∈ I,
          coeff i * (endpoint i : ℝ) *
            (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
              rho (FriableAsymptotic.dickmanU base y))| ≤
        ∑ i ∈ I,
          |coeff i| * (endpoint i : ℝ) *
            |FriableAsymptotic.dickmanU (endpoint i) y -
              FriableAsymptotic.dickmanU base y| := by
    calc
      _ ≤ ∑ i ∈ I,
          |coeff i * (endpoint i : ℝ) *
            (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
              rho (FriableAsymptotic.dickmanU base y))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ I,
          |coeff i| * (endpoint i : ℝ) *
            |FriableAsymptotic.dickmanU (endpoint i) y -
              FriableAsymptotic.dickmanU base y| := by
        apply Finset.sum_le_sum
        intro i hi
        have hendpointAbs : |(endpoint i : ℝ)| = (endpoint i : ℝ) :=
          abs_of_nonneg (Nat.cast_nonneg _)
        rw [abs_mul, abs_mul, hendpointAbs]
        exact mul_le_mul_of_nonneg_left
          (roughRho_abs_sub_le_abs_of_le_five
            (hendpoint5 i hi) hbase5)
          (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have hrhoPos : 0 < rho (FriableAsymptotic.dickmanU base y) :=
    rho_pos_on_zero_five hbase0 hbase5
  have hrhoLe : rho (FriableAsymptotic.dickmanU base y) ≤ 1 :=
    FriableAsymptotic.rho_le_one_of_le_five hbase5
  rw [hcenter]
  calc
    |(∑ i ∈ I,
          coeff i * (endpoint i : ℝ) *
            (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
              rho (FriableAsymptotic.dickmanU base y))) +
        rho (FriableAsymptotic.dickmanU base y) *
          ∑ i ∈ I, coeff i * (endpoint i : ℝ)| ≤
      |∑ i ∈ I,
          coeff i * (endpoint i : ℝ) *
            (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
              rho (FriableAsymptotic.dickmanU base y))| +
        |rho (FriableAsymptotic.dickmanU base y) *
          ∑ i ∈ I, coeff i * (endpoint i : ℝ)| := abs_add_le _ _
    _ ≤ (∑ i ∈ I,
          |coeff i| * (endpoint i : ℝ) *
            |FriableAsymptotic.dickmanU (endpoint i) y -
              FriableAsymptotic.dickmanU base y|) +
        |∑ i ∈ I, coeff i * (endpoint i : ℝ)| := by
      apply add_le_add hcenterBound
      rw [abs_mul, abs_of_pos hrhoPos]
      calc
        rho (FriableAsymptotic.dickmanU base y) *
            |∑ i ∈ I, coeff i * (endpoint i : ℝ)| ≤
          1 * |∑ i ∈ I, coeff i * (endpoint i : ℝ)| :=
            mul_le_mul_of_nonneg_right hrhoLe (abs_nonneg _)
        _ = |∑ i ∈ I, coeff i * (endpoint i : ℝ)| := one_mul _

/-! ## The literal four-endpoint residual collapse -/











/-! ## The one remaining analytic inequality -/







end

end Erdos390.WholePaper

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal008_022.{u_1} := by
  exact @Erdos390.WholePaper.roughFriableMain_abs_le_with_balanceError
