-- Prove2me | Theorems.Thm_Erdos390_Full_SquarefreeCovarianceReference_abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles
-- name    : Erdos390.Full.SquarefreeCovarianceReference.abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:29:30.953364+00:00
-- url     : https://prove2.me/theorems/3f550579-70b7-497b-9697-42f31894ee45
-- title:
--   Signed off-diagonal covariance comparison for a finite mixture
-- statement:
--   Let $\mu$ be an arbitrary probability mixture of finitely many bounded valuation laws, $n>1$, and distinct moving-band primes $p,q$. Suppose every component's expectations of $1_{pq\mid m},1_{p\mid m},1_{q\mid m}$ differ from the common paper divisibility main terms by at most $4E/(pq),2E/p,2E/q$, respectively, with $E\ge0$. Write $a=1/\rho(U)$, $t_p=\log p/\log y(n)$, and $K$ for the Dickman covariance kernel. Then
--   $$\left|\operatorname{Cov}_\mu(1_{p\mid m},1_{q\mid m})-\frac{K(t_p,t_q)}{pq}\right|\le\bigl[E(1+2a)+E^2\bigr]\frac4{pq}.$$
--   This is a signed comparison for the full mixture, retaining between-cell covariance. The moving prime band is $\{p\text{ prime}:W<p\le\lfloor n^{2/9}\rfloor\}$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/SquarefreeCovarianceReference.lean#L57-L171

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

theorem Erdos390.Full.SquarefreeCovarianceReference.abs_sigmaMixture_covII_sub_squarefreeKernelEntry_le_of_squarefree_profiles :
∀ {Cell : Type u_1} [inst : Fintype.{u_1} Cell] {Omega : Cell → Type u_2}
  [inst_1 : (c : Cell) → Fintype.{u_2} (Omega c)] {M : Nat} {E : Real},
  LE.le.{0} (0 : Real) E →
    ∀ (weight : Erdos390.Full.FiniteProbability.{u_1} Cell)
      (law : (c : Cell) → Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_2} (Omega c) M) {n W p q : Nat},
      LT.lt.{0} (1 : Nat) n →
        Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
          Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
            (∀ (c : Cell),
                LE.le.{0}
                  (abs.{0}
                    (HSub.hSub.{0, 0, 0}
                      (Erdos390.Full.FiniteProbability.expect.{u_2}
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_2} (law c)) fun omega =>
                        Erdos390.Full.ArithmeticModel.divInd
                          (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat))
                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_2} (law c) omega))
                      (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n
                        (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)))))
                  (HMul.hMul.{0, 0, 0} E
                    (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q (1 : Nat) (1 : Nat)))) →
              (∀ (c : Cell),
                  LE.le.{0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.FiniteProbability.expect.{u_2}
                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_2} (law c))
                          fun omega =>
                          Erdos390.Full.ArithmeticModel.divInd p
                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_2} (law c) omega))
                        (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n p)))
                    (HMul.hMul.{0, 0, 0} E (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat)))) →
                (∀ (c : Cell),
                    LE.le.{0}
                      (abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.FiniteProbability.expect.{u_2}
                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_2} (law c))
                            fun omega =>
                            Erdos390.Full.ArithmeticModel.divInd q
                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_2} (law c) omega))
                          (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n q)))
                      (HMul.hMul.{0, 0, 0} E (Erdos390.Full.PaperPrimePowerChamberError.singleWeight q (1 : Nat)))) →
                  have mix := Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.sigmaMixture.{u_1, u_2} weight law;
                  LE.le.{0}
                    (abs.{0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{max u_1 u_2} mix p q)
                        (Erdos390.Full.SquarefreeCovarianceReference.squarefreeKernelEntry n p q)))
                    (HMul.hMul.{0, 0, 0} (Erdos390.Full.PaperPrimePowerChamberError.pairCovarianceScale E)
                      (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q (1 : Nat) (1 : Nat))) := by sorry
