-- Prove2me | Theorems.Thm_Erdos390_Full_FixedFiniteMixturePrimePower_abs_sigmaMixture_primePower_covariance_le_of_common_profile
-- name    : Erdos390.Full.FixedFiniteMixturePrimePower.abs_sigmaMixture_primePower_covariance_le_of_common_profile
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T14:54:17.444295+00:00
-- url     : https://prove2.me/theorems/653dc978-97fd-4767-ab75-d31fbf0f0273
-- title:
--   Prime-power covariance in a mixture with a common profile
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, $U=9/2$, and $v_d=U-\log d/\log y$. Let $\rho$ denote the Dickman function. Let $F(x)=\rho(U-x)/\rho(U)$ and suppose $|F(x+z)-F(x)F(z)|\le C_Kxz$ for $x,z\ge0$, $x+z\le4$. Let a finite probability weight mix bounded-valuation laws with the same physical bound. Fix $n>1$, distinct primes $p,q$ in $(W,Y]$, and exponents $r,s$ with $p^rq^s\le Y^4$. Suppose every component law, for all $u,v$ with $p^uq^v\le Y^4$, differs from the common divisor main term by at most $E(u+1)(v+1)/(p^uq^v)$, where $E\ge0$. Put $t_p=\log p/\log y$ and $t_q=\log q/\log y$.
--
--   $$|\operatorname{Cov}_{\rm mix}(\mathbf1_{p^r\mid m},\mathbf1_{q^s\mid m})|\le\frac{C_K(rt_p)(st_q)}{p^rq^s}+\left(E\left(1+\frac2{\rho(U)}\right)+E^2\right)\frac{(r+1)(s+1)}{p^rq^s}.$$
--
--   The argument estimates probabilities before forming covariance, so variation between component laws is included.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/FixedFiniteMixturePrimePower.lean#L30-L143

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

universe u_1 u_2

theorem Erdos390.Full.FixedFiniteMixturePrimePower.abs_sigmaMixture_primePower_covariance_le_of_common_profile :
∀ {Cell : Type u_1} [inst : Fintype.{u_1} Cell] {Omega : Cell → Type u_2}
  [inst_1 : (c : Cell) → Fintype.{u_2} (Omega c)] {M : Nat} {C_K E : Real},
  (∀ (x z : Real),
      LE.le.{0} (0 : Real) x →
        LE.le.{0} (0 : Real) z →
          LE.le.{0} (HAdd.hAdd.{0, 0, 0} x z) (4 : Real) →
            LE.le.{0}
              (abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.DickmanFourMarkProductKernel.fourMarkProfile (HAdd.hAdd.{0, 0, 0} x z))
                  (HMul.hMul.{0, 0, 0} (Erdos390.Full.DickmanFourMarkProductKernel.fourMarkProfile x)
                    (Erdos390.Full.DickmanFourMarkProductKernel.fourMarkProfile z))))
              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C_K x) z)) →
    LE.le.{0} (0 : Real) E →
      ∀ (weight : Erdos390.Full.FiniteProbability.{u_1} Cell)
        (law : (c : Cell) → Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_2} (Omega c) M)
        {n W p q r s : Nat},
        LT.lt.{0} (1 : Nat) n →
          Membership.mem.{0, 0} (Erdos390.Full.ArithmeticModel.primeBand n W) p →
            Membership.mem.{0, 0} (Finset.erase.{0} (Erdos390.Full.ArithmeticModel.primeBand n W) p) q →
              LE.le.{0} (Erdos390.Full.OmittedTiltPairChamber.pairPower p q r s)
                  (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
                (∀ (c : Cell) (u v : Nat),
                    LE.le.{0} (Erdos390.Full.OmittedTiltPairChamber.pairPower p q u v)
                        (HPow.hPow.{0, 0, 0} (Erdos390.Full.ArithmeticModel.yNat n) (4 : Nat)) →
                      LE.le.{0}
                        (abs.{0}
                          (HSub.hSub.{0, 0, 0}
                            (Erdos390.Full.FiniteProbability.expect.{u_2}
                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_2} (law c))
                              fun omega =>
                              Erdos390.Full.ArithmeticModel.divInd
                                (Erdos390.Full.OmittedTiltPairChamber.pairPower p q u v)
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_2} (law c) omega))
                            (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain n
                              (Erdos390.Full.OmittedTiltPairChamber.pairPower p q u v))))
                        (HMul.hMul.{0, 0, 0} E (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q u v))) →
                  have mix := Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.sigmaMixture.{u_1, u_2} weight law;
                  LE.le.{0}
                    (abs.{0}
                      (Erdos390.Full.FiniteProbability.covariance.{max u_1 u_2}
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{max u_1 u_2} mix)
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{max u_1 u_2} mix p r)
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.Ip.{max u_1 u_2} mix q s)))
                    (HAdd.hAdd.{0, 0, 0}
                      (HDiv.hDiv.{0, 0, 0}
                        (HMul.hMul.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} C_K
                            (HMul.hMul.{0, 0, 0} (↑r) (Erdos390.Full.ArithmeticModel.tPrime n p)))
                          (HMul.hMul.{0, 0, 0} (↑s) (Erdos390.Full.ArithmeticModel.tPrime n q)))
                        (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑p) r) (HPow.hPow.{0, 0, 0} (↑q) s)))
                      (HMul.hMul.{0, 0, 0} (Erdos390.Full.PaperPrimePowerChamberError.pairCovarianceScale E)
                        (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q r s))) := by sorry
