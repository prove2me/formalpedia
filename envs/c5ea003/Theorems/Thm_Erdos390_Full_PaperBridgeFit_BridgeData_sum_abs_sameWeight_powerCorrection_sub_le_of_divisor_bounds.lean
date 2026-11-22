-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_sum_abs_sameWeight_powerCorrection_sub_le_of_divisor_bounds
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_sameWeight_powerCorrection_sub_le_of_divisor_bounds
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:29:55.109805+00:00
-- url     : https://prove2.me/theorems/fd3eb376-62c0-42a3-a4ee-cc15abb61368
-- title:
--   Divisor perturbations control a common-mixture power row
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, and $\mathcal P=\{p\text{ prime}:W<p\le Y\}$. For a valuation law $\lambda$, put $\Delta_\lambda(p,q)=\operatorname{Cov}_\lambda(v_p,v_q)-\operatorname{Cov}_\lambda(\mathbf1_{p\mid m},\mathbf1_{q\mid m})$. Let common finite weights mix pairs of bounded-valuation laws $\mu_c,\nu_c$ with common bound $M$, and let $W>1$, $\epsilon,G\ge0$. Suppose for all cells and positive $D$, $\mathbb E_{\mu_c}\mathbf1_{D\mid m}\le G/D$ and the two divisor probabilities differ by at most $8\epsilon G/D$. Suppose their divisor-pair covariances differ by at most $8\epsilon(G/\operatorname{lcm}(D,E)+3G^2/(DE))$ for every positive $D,E$. Then
--
--   $$\sum_{q\in\mathcal P}|\Delta_\nu(p,q)-\Delta_\mu(p,q)|\le\mathrm{physicalPowerCorrectionMixtureBudget}(\epsilon,G,n,W,p).$$
--
--   This is the finite core of the residual physical-score comparison.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperBridgePhysicalPowerCorrectionRow.lean#L1123-L1345

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

universe u_3 u_4

theorem Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_sameWeight_powerCorrection_sub_le_of_divisor_bounds :
∀ {Cell : Type u_3} [inst : Fintype.{u_3} Cell] {Omega : Cell → Type u_4}
  [inst_1 : (c : Cell) → Fintype.{u_4} (Omega c)] {M n W : Nat} (weight : Erdos390.Full.FiniteProbability.{u_3} Cell)
  (mu nu : (c : Cell) → Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_4} (Omega c) M)
  (p : Erdos390.Full.ArithmeticBandGeometry.BandPrime n W) {epsilon G : Real},
  LE.le.{0} (0 : Real) epsilon →
    LE.le.{0} (0 : Real) G →
      LT.lt.{0} (1 : Nat) W →
        (∀ (c : Cell) (D : Nat),
            LT.lt.{0} (0 : Nat) D →
              LE.le.{0}
                (Erdos390.Full.FiniteProbability.expect.{u_4}
                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_4} (mu c)) fun (x : Omega c) =>
                  Erdos390.Full.ArithmeticModel.divInd D
                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} (mu c) x))
                (HMul.hMul.{0, 0, 0} G (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑D : Real)))) →
          (∀ (c : Cell) (D : Nat),
              LT.lt.{0} (0 : Nat) D →
                LE.le.{0}
                  (abs.{0}
                    (HSub.hSub.{0, 0, 0}
                      (Erdos390.Full.FiniteProbability.expect.{u_4}
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_4} (nu c))
                        fun (x : Omega c) =>
                        Erdos390.Full.ArithmeticModel.divInd D
                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} (nu c) x))
                      (Erdos390.Full.FiniteProbability.expect.{u_4}
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_4} (mu c))
                        fun (x : Omega c) =>
                        Erdos390.Full.ArithmeticModel.divInd D
                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} (mu c) x))))
                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (8 : Real) epsilon) G)
                    (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑D : Real)))) →
            (∀ (c : Cell) (D E : Nat),
                LT.lt.{0} (0 : Nat) D →
                  LT.lt.{0} (0 : Nat) E →
                    LE.le.{0}
                      (abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.FiniteProbability.covariance.{u_4}
                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_4} (nu c))
                            (fun (x : Omega c) =>
                              Erdos390.Full.ArithmeticModel.divInd D
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} (nu c) x))
                            fun (x : Omega c) =>
                            Erdos390.Full.ArithmeticModel.divInd E
                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} (nu c) x))
                          (Erdos390.Full.FiniteProbability.covariance.{u_4}
                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{u_4} (mu c))
                            (fun (x : Omega c) =>
                              Erdos390.Full.ArithmeticModel.divInd D
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} (mu c) x))
                            fun (x : Omega c) =>
                            Erdos390.Full.ArithmeticModel.divInd E
                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{u_4} (mu c) x))))
                      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (8 : Real) epsilon)
                        (HAdd.hAdd.{0, 0, 0}
                          (HMul.hMul.{0, 0, 0} G (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑(Nat.lcm D E) : Real)))
                          (HMul.hMul.{0, 0, 0}
                            (HMul.hMul.{0, 0, 0} (3 : Real)
                              (HMul.hMul.{0, 0, 0} G (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑D : Real))))
                            (HMul.hMul.{0, 0, 0} G (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑E : Real))))))) →
              LE.le.{0}
                (∑ q : Erdos390.Full.ArithmeticBandGeometry.BandPrime n W,
                  abs.{0}
                    (HSub.hSub.{0, 0, 0}
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{max u_3 u_4}
                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.sigmaMixture.{u_3, u_4} weight nu)
                          (↑p : Nat) (↑q : Nat))
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{max u_3 u_4}
                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.sigmaMixture.{u_3, u_4} weight nu)
                          (↑p : Nat) (↑q : Nat)))
                      (HSub.hSub.{0, 0, 0}
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{max u_3 u_4}
                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.sigmaMixture.{u_3, u_4} weight mu)
                          (↑p : Nat) (↑q : Nat))
                        (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{max u_3 u_4}
                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.sigmaMixture.{u_3, u_4} weight mu)
                          (↑p : Nat) (↑q : Nat)))))
                (Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionMixtureBudget epsilon G n W (↑p : Nat)) := by sorry
