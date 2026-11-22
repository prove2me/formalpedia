-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumOrderedMixtureMain_eq_mixtureIntegralMain_of_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:54:08.469167+00:00
-- url     : https://prove2.me/submissions/ad83aa3a-1797-45af-a0f8-b7da6429d9f1

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_009

/- Source module: Erdos390.WholePaper.BankPaperFourFiveOrderedMixtureAssembly -/
section


/-!
# Final factorial assembly for the ordered four/five mixture

This file is the algebraic terminus of the ordered-prime calculation.  It
defines the four fixed-simplex continuum layer mains, records the exact
`1, 1/2!, 1/3!, 1/4!` error ledger, and turns four layerwise estimates into
the repository's `FourFiveOrderedPrimeMixtureEstimate` proposition.

The second assembly theorem plugs in the exact last-prime endpoint estimates
from `BankPaperFourFiveOrderedLastPrimeExpansion`.  Its only remaining input
is the displayed four-layer bridge from the last-prime logarithmic integrals
to the fixed-simplex continuum layers.  The bridge budget exposes separately
the already-proved moving-face telescope losses

`0, 2 E, 4 E M, 6 E M^2`

and user-supplied cell-quadrature losses.  Thus the still-missing analytic
step is explicit in the theorem statement rather than hidden in a new axiom.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

/-! ## The four fixed-simplex layer main terms -/













/-- The layerwise and single-integral presentations agree whenever the four
layer integrands are interval-integrable.  This is finite linearity of the
outer integral; no Fubini interchange is involved. -/
theorem
    fourFiveContinuumOrderedMixtureMain_eq_mixtureIntegralMain_of_intervalIntegrable
    {y A B : Nat}
    (h1 : IntervalIntegrable
      (fun t : Real => fourFiveContinuumKernelOne
        (Real.log t / Real.log (y : Real)))
      MeasureTheory.volume (A : Real) (B : Real))
    (h2 : IntervalIntegrable
      (fun t : Real => fourFiveContinuumKernelTwo
        (Real.log t / Real.log (y : Real)))
      MeasureTheory.volume (A : Real) (B : Real))
    (h3 : IntervalIntegrable
      (fun t : Real => fourFiveContinuumKernelThree
        (Real.log t / Real.log (y : Real)))
      MeasureTheory.volume (A : Real) (B : Real))
    (h4 : IntervalIntegrable
      (fun t : Real => fourFiveContinuumKernelFour
        (Real.log t / Real.log (y : Real)))
      MeasureTheory.volume (A : Real) (B : Real)) :
    fourFiveContinuumOrderedMixtureMain y A B =
      fourFiveContinuumMixtureIntegralMain y A B := by
  have h12 := h1.add (h2.div_const 2)
  have h123 := h12.add (h3.div_const 6)
  have hintegral :
      (∫ t in (A : Real)..(B : Real),
        fourFiveContinuumMixtureKernel
          (Real.log t / Real.log (y : Real))) =
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelOne
            (Real.log t / Real.log (y : Real))) +
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelTwo
            (Real.log t / Real.log (y : Real))) / 2 +
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelThree
            (Real.log t / Real.log (y : Real))) / 6 +
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelFour
            (Real.log t / Real.log (y : Real))) / 24 := by
    unfold fourFiveContinuumMixtureKernel
    calc
      (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelOne
              (Real.log t / Real.log (y : Real)) +
            fourFiveContinuumKernelTwo
                (Real.log t / Real.log (y : Real)) / 2 +
            fourFiveContinuumKernelThree
                (Real.log t / Real.log (y : Real)) / 6 +
            fourFiveContinuumKernelFour
                (Real.log t / Real.log (y : Real)) / 24) =
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelOne
                (Real.log t / Real.log (y : Real)) +
              fourFiveContinuumKernelTwo
                  (Real.log t / Real.log (y : Real)) / 2 +
              fourFiveContinuumKernelThree
                  (Real.log t / Real.log (y : Real)) / 6) +
          ∫ t in (A : Real)..(B : Real),
            fourFiveContinuumKernelFour
              (Real.log t / Real.log (y : Real)) / 24 :=
        intervalIntegral.integral_add h123 (h4.div_const 24)
      _ =
        ((∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelOne
                (Real.log t / Real.log (y : Real)) +
              fourFiveContinuumKernelTwo
                (Real.log t / Real.log (y : Real)) / 2) +
            ∫ t in (A : Real)..(B : Real),
              fourFiveContinuumKernelThree
                (Real.log t / Real.log (y : Real)) / 6) +
          ∫ t in (A : Real)..(B : Real),
            fourFiveContinuumKernelFour
              (Real.log t / Real.log (y : Real)) / 24 := by
        exact congrArg
          (fun z : Real => z +
            (∫ t in (A : Real)..(B : Real),
              fourFiveContinuumKernelFour
                (Real.log t / Real.log (y : Real)) / 24))
          (intervalIntegral.integral_add h12 (h3.div_const 6))
      _ =
        (((∫ t in (A : Real)..(B : Real),
            fourFiveContinuumKernelOne
              (Real.log t / Real.log (y : Real))) +
            ∫ t in (A : Real)..(B : Real),
              fourFiveContinuumKernelTwo
                (Real.log t / Real.log (y : Real)) / 2) +
            ∫ t in (A : Real)..(B : Real),
              fourFiveContinuumKernelThree
                (Real.log t / Real.log (y : Real)) / 6) +
          ∫ t in (A : Real)..(B : Real),
            fourFiveContinuumKernelFour
              (Real.log t / Real.log (y : Real)) / 24 := by
        exact congrArg
          (fun z : Real =>
            (z +
              (∫ t in (A : Real)..(B : Real),
                fourFiveContinuumKernelThree
                  (Real.log t / Real.log (y : Real)) / 6)) +
            (∫ t in (A : Real)..(B : Real),
              fourFiveContinuumKernelFour
                (Real.log t / Real.log (y : Real)) / 24))
          (intervalIntegral.integral_add h1 (h2.div_const 2))
      _ =
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelOne
            (Real.log t / Real.log (y : Real))) +
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelTwo
            (Real.log t / Real.log (y : Real))) / 2 +
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelThree
            (Real.log t / Real.log (y : Real))) / 6 +
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelFour
            (Real.log t / Real.log (y : Real))) / 24 := by
        simp only [intervalIntegral.integral_div]
  calc
    fourFiveContinuumOrderedMixtureMain y A B =
        (1 / Real.log (y : Real)) *
          ((∫ t in (A : Real)..(B : Real),
            fourFiveContinuumKernelOne
              (Real.log t / Real.log (y : Real))) +
          (∫ t in (A : Real)..(B : Real),
            fourFiveContinuumKernelTwo
              (Real.log t / Real.log (y : Real))) / 2 +
          (∫ t in (A : Real)..(B : Real),
            fourFiveContinuumKernelThree
              (Real.log t / Real.log (y : Real))) / 6 +
          (∫ t in (A : Real)..(B : Real),
            fourFiveContinuumKernelFour
              (Real.log t / Real.log (y : Real))) / 24) := by
      unfold fourFiveContinuumOrderedMixtureMain
        fourFiveContinuumLayerOneMain fourFiveContinuumLayerTwoMain
        fourFiveContinuumLayerThreeMain fourFiveContinuumLayerFourMain
      ring
    _ = (1 / Real.log (y : Real)) *
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumMixtureKernel
            (Real.log t / Real.log (y : Real))) :=
      congrArg (fun z : Real => (1 / Real.log (y : Real)) * z)
        hintegral.symm
    _ = fourFiveContinuumMixtureIntegralMain y A B := by
      rfl







/-! ## Pure factorial error assembly -/



/-! ## The exact remaining bridge contract -/











end Erdos390.WholePaper.BankPaperRealization

end

theorem solution :
∀ {y A B : Nat},
  IntervalIntegrable.{0}
      (fun t =>
        Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumKernelOne
          (HDiv.hDiv.{0, 0, 0} (Real.log t) (Real.log ↑y)))
      MeasureTheory.MeasureSpace.volume.{0} ↑A ↑B →
    IntervalIntegrable.{0}
        (fun t =>
          Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumKernelTwo
            (HDiv.hDiv.{0, 0, 0} (Real.log t) (Real.log ↑y)))
        MeasureTheory.MeasureSpace.volume.{0} ↑A ↑B →
      IntervalIntegrable.{0}
          (fun t =>
            Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumKernelThree
              (HDiv.hDiv.{0, 0, 0} (Real.log t) (Real.log ↑y)))
          MeasureTheory.MeasureSpace.volume.{0} ↑A ↑B →
        IntervalIntegrable.{0}
            (fun t =>
              Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumKernelFour
                (HDiv.hDiv.{0, 0, 0} (Real.log t) (Real.log ↑y)))
            MeasureTheory.MeasureSpace.volume.{0} ↑A ↑B →
          Eq.{1} (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumOrderedMixtureMain y A B)
            (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumMixtureIntegralMain y A B) := by
  exact @Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumOrderedMixtureMain_eq_mixtureIntegralMain_of_intervalIntegrable
