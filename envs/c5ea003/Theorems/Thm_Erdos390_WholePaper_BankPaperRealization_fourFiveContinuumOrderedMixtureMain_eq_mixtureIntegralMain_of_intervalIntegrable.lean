-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_fourFiveContinuumOrderedMixtureMain_eq_mixtureIntegralMain_of_intervalIntegrable
-- name    : Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumOrderedMixtureMain_eq_mixtureIntegralMain_of_intervalIntegrable
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:53:50.019575+00:00
-- url     : https://prove2.me/theorems/1e6b55a7-4c4e-4297-bf37-fd9c8d63f05e
-- title:
--   The four continuum layers equal one factorial-mixture integral
-- statement:
--   Let $y,A,B$ be natural numbers. Write $K_1,K_2,K_3,K_4$ for the source's four continuum layer kernels. Assume each function $t\mapsto K_j(\log t/\log y)$ is interval-integrable between $A$ and $B$. Then
--   $$\sum_{j=1}^4\frac1{j!\log y}\int_A^B K_j\!\left(\frac{\log t}{\log y}\right)\,dt=\frac1{\log y}\int_A^B\left[\sum_{j=1}^4\frac1{j!}K_j\!\left(\frac{\log t}{\log y}\right)\right]dt.$$
--   In the source notation, the ordered continuum mixture main equals the mixture-integral main. This identifies the two presentations using only finite linearity of the outer integral.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperFourFiveOrderedMixtureAssembly.lean#L72-L217

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_009

theorem Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumOrderedMixtureMain_eq_mixtureIntegralMain_of_intervalIntegrable :
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
            (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumMixtureIntegralMain y A B) := by sorry
