-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_roughCoreDiscreteVariation_fourFiveFrozenKernelWeight_le
-- name    : Erdos390.WholePaper.BankPaperRealization.roughCoreDiscreteVariation_fourFiveFrozenKernelWeight_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:01:21.894842+00:00
-- url     : https://prove2.me/theorems/d62a1b45-29d0-465b-80a5-a624d0335d53
-- title:
--   Discrete variation bound for the frozen four/five kernel weight
-- statement:
--   Write $Y_n=\lfloor n^{2/9}\rfloor$. Let $n,D>0$, $B\in\mathbb N$, $\log Y_n\ge1$, and $C\ge0$. Assume the mixture kernel $K$ and its derivative are bounded in absolute value by $C$ on $[41/10,47/10]$, and $u_{Dm}=\log(2n/(Dm))/\log Y_n$ lies there for all $1\le m\le B$. Put $F(m)=K(u_{Dm})/(Dm)$ for positive $m$. For $B>0$,
--
--   $$|F(B)|+\sum_{m=1}^{B-1}|F(m)-F(m+1)|\le2C/D.$$
--
--   For $B=0$, the source discrete variation is zero and the same bound holds.
--
--   This is the variation input for core-first summation with periodic coefficients.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalFourFiveKernelVariation.lean#L190-L366

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_009

theorem Erdos390.WholePaper.BankPaperRealization.roughCoreDiscreteVariation_fourFiveFrozenKernelWeight_le :
∀ {n D B : Nat} {C : Real},
  LT.lt.{0} (0 : Nat) n →
    LT.lt.{0} (0 : Nat) D →
      LE.le.{0} (1 : Real) (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)) →
        LE.le.{0} (0 : Real) C →
          (∀ (z : Real),
              Membership.mem.{0, 0} (Set.Icc.{0} (41 / 10 : Real) (47 / 10 : Real)) z →
                And (LE.le.{0} (abs.{0} (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumMixtureKernel z)) C)
                  (LE.le.{0}
                    (abs.{0} (Erdos390.WholePaper.BankPaperRealization.fourFiveContinuumMixtureKernelDerivative z))
                    C)) →
            (∀ (m : Nat),
                Membership.mem.{0, 0} (Finset.Icc.{0} (1 : Nat) B) m →
                  Membership.mem.{0, 0} (Set.Icc.{0} (41 / 10 : Real) (47 / 10 : Real))
                    (Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveFrozenCoordinate n
                      (HMul.hMul.{0, 0, 0} D m))) →
              LE.le.{0}
                (Erdos390.WholePaper.BankPaperRealization.roughCoreDiscreteVariation
                  (fun m =>
                    Erdos390.WholePaper.BankPaperRealization.roughCanonicalFourFiveFrozenKernelWeight n
                      (HMul.hMul.{0, 0, 0} D m))
                  B)
                (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) C) ↑D) := by sorry
