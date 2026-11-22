-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.fourFiveRightDiscreteBVNorm_cutoffSequence_le_two
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:58:13.741557+00:00
-- url     : https://prove2.me/submissions/2766301b-f971-41ba-a38c-ec139ff01327

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_009

/- Source module: Erdos390.WholePaper.BankPaperFourFiveMovingFaceBV -/
section


/-!
# Moving-face mass and bounded-variation certificates

For fixed values of all but one logarithmic prime coordinate, the simplex
kernel is increasing until the moving face and is zero afterwards.  Its
height is at most one because the omitted last-prime coordinate has
logarithmic size at least one.  Thus its right-endpoint-plus-variation norm
is at most two: at most one unit while increasing and at most one unit for
the unique cutoff jump.

This file proves that finite statement first for an abstract monotone
sequence, then instantiates it for the literal logarithmic moving-face
kernel.  The one-, two-, and three-coordinate kernels are finally fed into
the product-measure telescope with `V = 2`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open Erdos390.Full.PrimeSums

/-! ## A finite one-jump BV lemma -/





/-- An increasing sequence bounded between zero and one, stopped after a
single natural cutoff, has paper BV norm at most two. -/
theorem fourFiveRightDiscreteBVNorm_cutoffSequence_le_two
    (g : Nat -> Real) {A R Y : Nat} (hAY : A <= Y)
    (hmono : ∀ a ∈ Finset.Icc A Y,
      ∀ b ∈ Finset.Icc A Y, a <= b -> g a <= g b)
    (hnonneg : ∀ n ∈ Finset.Icc A Y, 0 <= g n)
    (hone : ∀ n ∈ Finset.Icc A Y, g n <= 1) :
    fourFiveRightDiscreteBVNorm
        (fourFiveCutoffSequence A R g) A Y <= 2 := by
  by_cases hAYlt : A < Y
  · have hsuccAY : A + 1 <= Y := by omega
    have hinterval : Finset.Ioc A (Y - 1) = Finset.Ico (A + 1) Y := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    have hA1mem : A + 1 ∈ Finset.Icc A Y :=
      Finset.mem_Icc.mpr ⟨by omega, hsuccAY⟩
    have hYmem : Y ∈ Finset.Icc A Y :=
      Finset.mem_Icc.mpr ⟨hAY, le_rfl⟩
    by_cases hYR : Y <= R
    · have hvariation :
          (∑ n ∈ Finset.Ioc A (Y - 1),
            |fourFiveCutoffSequence A R g (n + 1) -
              fourFiveCutoffSequence A R g n|) =
            g Y - g (A + 1) := by
        rw [hinterval]
        calc
          (∑ n ∈ Finset.Ico (A + 1) Y,
              |fourFiveCutoffSequence A R g (n + 1) -
                fourFiveCutoffSequence A R g n|) =
              ∑ n ∈ Finset.Ico (A + 1) Y,
                (g (n + 1) - g n) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hnData := Finset.mem_Ico.mp hn
            have hnMem : n ∈ Finset.Icc A Y :=
              Finset.mem_Icc.mpr ⟨by omega, hnData.2.le⟩
            have hn1Mem : n + 1 ∈ Finset.Icc A Y :=
              Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            have hnR : n <= R := hnData.2.le.trans hYR
            have hn1R : n + 1 <= R := by omega
            have hnActive : A < n ∧ n <= R := by
              exact ⟨by omega, hnR⟩
            have hn1Active : A < n + 1 ∧ n + 1 <= R := by
              exact ⟨by omega, hn1R⟩
            have hcutn : fourFiveCutoffSequence A R g n = g n := by
              rw [fourFiveCutoffSequence, if_pos hnActive]
            have hcutn1 :
                fourFiveCutoffSequence A R g (n + 1) = g (n + 1) := by
              rw [fourFiveCutoffSequence, if_pos hn1Active]
            have hdiff : 0 <= g (n + 1) - g n :=
              sub_nonneg.mpr (hmono n hnMem (n + 1) hn1Mem (by omega))
            rw [hcutn1, hcutn, abs_of_nonneg hdiff]
          _ = g Y - g (A + 1) :=
            Finset.sum_Ico_sub g hsuccAY
      unfold fourFiveRightDiscreteBVNorm
      rw [hvariation]
      have hcutY : fourFiveCutoffSequence A R g Y = g Y := by
        simp [fourFiveCutoffSequence, hAYlt, hYR]
      rw [hcutY, abs_of_nonneg (hnonneg Y hYmem)]
      linarith [hone Y hYmem, hnonneg (A + 1) hA1mem]
    · have hstep : ∀ n ∈ Finset.Ioc A (Y - 1),
          |fourFiveCutoffSequence A R g (n + 1) -
              fourFiveCutoffSequence A R g n| <=
            (g (n + 1) - g n) +
              (if n = R then 1 else 0) := by
        intro n hn
        have hnData := Finset.mem_Ioc.mp hn
        have hnMem : n ∈ Finset.Icc A Y :=
          Finset.mem_Icc.mpr ⟨hnData.1.le, by omega⟩
        have hn1Mem : n + 1 ∈ Finset.Icc A Y :=
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hgnMono : g n <= g (n + 1) :=
          hmono n hnMem (n + 1) hn1Mem (by omega)
        by_cases hnR : n <= R
        · by_cases hn1R : n + 1 <= R
          · have hnNe : n ≠ R := by omega
            have hnActive : A < n ∧ n <= R :=
              ⟨hnData.1, hnR⟩
            have hn1Active : A < n + 1 ∧ n + 1 <= R :=
              ⟨by omega, hn1R⟩
            have hcutn : fourFiveCutoffSequence A R g n = g n := by
              rw [fourFiveCutoffSequence, if_pos hnActive]
            have hcutn1 :
                fourFiveCutoffSequence A R g (n + 1) = g (n + 1) := by
              rw [fourFiveCutoffSequence, if_pos hn1Active]
            rw [hcutn1, hcutn, if_neg hnNe,
              abs_of_nonneg (sub_nonneg.mpr hgnMono), add_zero]
          · have hnEq : n = R := by omega
            subst n
            have hRMem : R ∈ Finset.Icc A Y := hnMem
            have hR1Mem : R + 1 ∈ Finset.Icc A Y := hn1Mem
            have hRActive : A < R ∧ R <= R :=
              ⟨hnData.1, le_rfl⟩
            have hR1Inactive : ¬(A < R + 1 ∧ R + 1 <= R) := by
              omega
            have hcutR : fourFiveCutoffSequence A R g R = g R := by
              rw [fourFiveCutoffSequence, if_pos hRActive]
            have hcutR1 :
                fourFiveCutoffSequence A R g (R + 1) = 0 := by
              rw [fourFiveCutoffSequence, if_neg hR1Inactive]
            rw [hcutR1, hcutR, if_pos rfl, zero_sub, abs_neg,
              abs_of_nonneg (hnonneg R hRMem)]
            linarith [hone R hRMem,
              hmono R hRMem (R + 1) hR1Mem (by omega)]
        · have hn1R : ¬n + 1 <= R := by omega
          have hnNe : n ≠ R := by omega
          have hnInactive : ¬(A < n ∧ n <= R) := by
            intro h
            exact hnR h.2
          have hn1Inactive : ¬(A < n + 1 ∧ n + 1 <= R) := by
            intro h
            exact hn1R h.2
          have hcutn : fourFiveCutoffSequence A R g n = 0 := by
            rw [fourFiveCutoffSequence, if_neg hnInactive]
          have hcutn1 :
              fourFiveCutoffSequence A R g (n + 1) = 0 := by
            rw [fourFiveCutoffSequence, if_neg hn1Inactive]
          rw [hcutn1, hcutn, sub_self, abs_zero, if_neg hnNe, add_zero]
          exact sub_nonneg.mpr hgnMono
      have hboundary :
          (∑ n ∈ Finset.Ioc A (Y - 1),
            (if n = R then (1 : Real) else 0)) <= 1 := by
        classical
        rw [Finset.sum_ite_eq']
        split_ifs <;> norm_num
      have hvariation :
          (∑ n ∈ Finset.Ioc A (Y - 1),
            |fourFiveCutoffSequence A R g (n + 1) -
              fourFiveCutoffSequence A R g n|) <= 2 := by
        calc
          (∑ n ∈ Finset.Ioc A (Y - 1),
              |fourFiveCutoffSequence A R g (n + 1) -
                fourFiveCutoffSequence A R g n|) <=
              ∑ n ∈ Finset.Ioc A (Y - 1),
                ((g (n + 1) - g n) +
                  (if n = R then 1 else 0)) := by
            apply Finset.sum_le_sum
            intro n hn
            exact hstep n hn
          _ = (g Y - g (A + 1)) +
              ∑ n ∈ Finset.Ioc A (Y - 1),
                (if n = R then 1 else 0) := by
            rw [Finset.sum_add_distrib, hinterval,
              Finset.sum_Ico_sub g hsuccAY]
          _ <= 2 := by
            linarith [hone Y hYmem, hnonneg (A + 1) hA1mem,
              hboundary]
      unfold fourFiveRightDiscreteBVNorm
      have hcutY : fourFiveCutoffSequence A R g Y = 0 := by
        simp [fourFiveCutoffSequence, show ¬Y <= R by omega]
      rw [hcutY, abs_zero, zero_add]
      exact hvariation
  · have hYA : Y = A := le_antisymm (not_lt.mp hAYlt) hAY
    subst Y
    unfold fourFiveRightDiscreteBVNorm
    have hempty : Finset.Ioc A (A - 1) = ∅ := by
      exact Finset.Ioc_eq_empty_of_le (by omega)
    rw [hempty]
    simp [fourFiveCutoffSequence]

/-! ## The literal logarithmic moving face -/

















/-!
The preceding certificate has an irrelevant `R < A` branch: the stopped
sequence is identically zero there.  Splitting that case first gives the
clean unconditional BV statement actually used below.
-/



/-! ## Compact reciprocal-mass bounds -/



















/-! ## One, two, and three moving-simplex coordinates -/



























/-! ## Literal product-telescope instantiations -/







end Erdos390.WholePaper.BankPaperRealization

end

theorem solution :
∀ (g : Nat → Real) {A R Y : Nat},
  LE.le.{0} A Y →
    (∀ (a : Nat),
        Membership.mem.{0, 0} (Finset.Icc.{0} A Y) a →
          ∀ (b : Nat), Membership.mem.{0, 0} (Finset.Icc.{0} A Y) b → LE.le.{0} a b → LE.le.{0} (g a) (g b)) →
      (∀ (n : Nat), Membership.mem.{0, 0} (Finset.Icc.{0} A Y) n → LE.le.{0} (0 : Real) (g n)) →
        (∀ (n : Nat), Membership.mem.{0, 0} (Finset.Icc.{0} A Y) n → LE.le.{0} (g n) (1 : Real)) →
          LE.le.{0}
            (Erdos390.WholePaper.BankPaperRealization.fourFiveRightDiscreteBVNorm
              (Erdos390.WholePaper.BankPaperRealization.fourFiveCutoffSequence A R g) A Y)
            (2 : Real) := by
  exact @Erdos390.WholePaper.BankPaperRealization.fourFiveRightDiscreteBVNorm_cutoffSequence_le_two
