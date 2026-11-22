-- Prove2me | Theorems.Thm_Erdos390_Full_SquarefreeCovarianceReference_abs_sigmaMixture_covII_diagonal_sub_reference_le
-- name    : Erdos390.Full.SquarefreeCovarianceReference.abs_sigmaMixture_covII_diagonal_sub_reference_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:28:49.358192+00:00
-- url     : https://prove2.me/theorems/d4ce97ee-4a83-4feb-a092-f21616e88dc4
-- title:
--   Signed diagonal covariance comparison with the squarefree reference
-- statement:
--   For a finite mixture $\mu$ of bounded valuation laws, let $n>1$ and $p$ be a moving-band prime. Assume every component has $|\mathbb P(p\mid m)-M_n(p)|\le2E/p$ with $E\ge0$, where $M_n$ is the paper divisibility main term. Suppose $|K(t_p,t_p)|\le C_K$ for the Dickman covariance kernel. With $a=1/\rho(U)$ and reference diagonal $R_{pp}=F(t_p)/p+K(t_p,t_p)/p^2$, one has
--   $$|\operatorname{Var}_\mu(1_{p\mid m})-R_{pp}|\le\frac{2E}{p}+\frac{(a+2E)^2+C_K}{p^2}.$$
--   The two scales separate the one-divisor profile error from the Bernoulli square and inserted kernel diagonal. The moving prime band is $\{p\text{ prime}:W<p\le\lfloor n^{2/9}\rfloor\}$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/SquarefreeCovarianceReference.lean#L208-L353

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

universe u_1 u_2

theorem Erdos390.Full.SquarefreeCovarianceReference.abs_sigmaMixture_covII_diagonal_sub_reference_le :
∀ {Cell : Type u_1} [inst : Fintype.{u_1} Cell] {Omega : Cell → Type u_2}
  [inst_1 : (c : Cell) → Fintype.{u_2} (Omega c)] {M : Nat} {E CKernel : Real},
  LE.le.{0} (0 : Real) E →
    ∀ (weight : Erdos390.Full.FiniteProbability.{u_1} Cell)
      (law : (c : Cell) → Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_2} (Omega c) M) {n W p : Nat},
      LT.lt.{0} (1 : Nat) n →
        Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
          (∀ (c : Cell),
              LE.le.{0}
                (abs.{0}
                  (HSub.hSub.{0, 0, 0}
                    (Erdos390.Full.FiniteProbability.expect.{u_2}
                      (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_2} (law c)) fun omega =>
                      Erdos390.Full.ArithmeticModel.divInd p
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_2} (law c) omega))
                    (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n p)))
                (HMul.hMul.{0, 0, 0} E (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat)))) →
            LE.le.{0}
                (abs.{0}
                  (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel (Erdos390.Full.ArithmeticModel.tPrime n p)
                    (Erdos390.Full.ArithmeticModel.tPrime n p)))
                CKernel →
              have mix := Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.sigmaMixture.{u_1, u_2} weight law;
              LE.le.{0}
                (abs.{0}
                  (HSub.hSub.{0, 0, 0}
                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{max u_1 u_2} mix p p)
                    (Erdos390.Full.SquarefreeCovarianceReference.squarefreeReferenceEntry n p p)))
                (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) E) ↑p)
                  (HDiv.hDiv.{0, 0, 0}
                    (HAdd.hAdd.{0, 0, 0}
                      (HPow.hPow.{0, 0, 0}
                        (HAdd.hAdd.{0, 0, 0}
                          (HDiv.hDiv.{0, 0, 0} (1 : Real) (Erdos390.Full.DickmanBasic.rho Erdos390.Full.DickmanBasic.U))
                          (HMul.hMul.{0, 0, 0} (2 : Real) E))
                        (2 : Nat))
                      CKernel)
                    (HPow.hPow.{0, 0, 0} ↑p (2 : Nat)))) := by sorry
