-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_abs_covJJ_sub_le_of_divisor_covariance_difference_of_ne
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.abs_covJJ_sub_le_of_divisor_covariance_difference_of_ne
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:12:09.101624+00:00
-- url     : https://prove2.me/theorems/89ced2fa-223b-43cd-9213-d2dc35debe61
-- title:
--   Distinct-prime higher-tail covariance perturbation
-- statement:
--   Let $\mu,\nu$ be bounded-valuation laws with the same physical bound, and let $p\ne q$ be primes. Suppose $e,G\ge0$ and every positive divisor pair satisfies $$|\operatorname{Cov}_\nu(\mathbf1_{D\mid m},\mathbf1_{E\mid m})-\operatorname{Cov}_\mu(\mathbf1_{D\mid m},\mathbf1_{E\mid m})|\le e\left(\frac G{\operatorname{lcm}(D,E)}+\frac{3G^2}{DE}\right).$$ Writing $J_p=v_p-\mathbf1_{p\mid m}$,
--
--   $$|\operatorname{Cov}_\nu(J_p,J_q)-\operatorname{Cov}_\mu(J_p,J_q)|\le\frac{e(4G+12G^2)}{p^2q^2}.$$
--
--   This provides the double-high component of the physical residual-tilt comparison.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperBridgePhysicalPowerCorrectionRow.lean#L702-L815

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002

universe u_3 u_4

theorem Erdos390.Full.PaperBridgeFit.BridgeData.abs_covJJ_sub_le_of_divisor_covariance_difference_of_ne :
∀ {Omega : Type u_3} {Theta : Type u_4} [inst : Fintype.{u_3} Omega] [inst_1 : Fintype.{u_4} Theta] {M p q : Nat}
  (nu : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_3} Omega M)
  (mu : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_4} Theta M),
  Nat.Prime p →
    Nat.Prime q →
      Ne.{1} p q →
        ∀ {e G : Real},
          LE.le.{0} (0 : Real) e →
            LE.le.{0} (0 : Real) G →
              (∀ (D E : Nat),
                  LT.lt.{0} (0 : Nat) D →
                    LT.lt.{0} (0 : Nat) E →
                      LE.le.{0}
                        (abs.{0}
                          (HSub.hSub.{0, 0, 0}
                            (Erdos390.Full.FiniteProbability.covariance.{u_3}
                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_3} nu)
                              (fun x =>
                                Erdos390.Full.ArithmeticModel.divInd D
                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_3} nu x))
                              fun x =>
                              Erdos390.Full.ArithmeticModel.divInd E
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_3} nu x))
                            (Erdos390.Full.FiniteProbability.covariance.{u_4}
                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_4} mu)
                              (fun x =>
                                Erdos390.Full.ArithmeticModel.divInd D
                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} mu x))
                              fun x =>
                              Erdos390.Full.ArithmeticModel.divInd E
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} mu x))))
                        (HMul.hMul.{0, 0, 0} e
                          (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} G (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑(Nat.lcm D E)))
                            (HMul.hMul.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0} (3 : Real)
                                (HMul.hMul.{0, 0, 0} G (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑D)))
                              (HMul.hMul.{0, 0, 0} G (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑E)))))) →
                LE.le.{0}
                  (abs.{0}
                    (HSub.hSub.{0, 0, 0} (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covJJ.{u_3} nu p q)
                      (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covJJ.{u_4} mu p q)))
                  (HMul.hMul.{0, 0, 0}
                    (HMul.hMul.{0, 0, 0}
                      (HMul.hMul.{0, 0, 0} e
                        (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) G)
                          (HMul.hMul.{0, 0, 0} (12 : Real) (HPow.hPow.{0, 0, 0} G (2 : Nat)))))
                      (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑p) (2 : Nat)))
                    (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (1 : Real) ↑q) (2 : Nat))) := by sorry
