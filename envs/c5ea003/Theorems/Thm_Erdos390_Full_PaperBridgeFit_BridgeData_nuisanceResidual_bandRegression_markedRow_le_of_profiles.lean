-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_nuisanceResidual_bandRegression_markedRow_le_of_profiles
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidual_bandRegression_markedRow_le_of_profiles
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:49:39.568816+00:00
-- url     : https://prove2.me/theorems/0b52a841-d704-4511-9a7a-1b2f73911cfe
-- title:
--   Nuisance-residual valuation row from finite signed profiles
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. Let $B$ be a bridge with finite head and band sets, and write $t_p=\log p/\log y_n$, $h_i$ for harmonic band masses, $\alpha_i$ for band centers, and $j(p)$ for the band of $p$. Let $R_{pr}$ be its squarefree Poisson–Dickman reference entry, $I_p=\mathbf1_{p\mid m}$, and $\mu_\xi$ its tilted law. Assume nonempty heads, $W>0$, and a nuisance covariance gap $\langle z,C_{\rm nuis}z\rangle\ge\gamma\|z\|^2$ with $\gamma>0$. Let $H,E,C_{\rm prod},C_m\ge0$, $\sum_i h_i\le H$, and $\sum_rt_r/r\le K_0$. In every component law assume the single-prime and distinct-prime pair divisibility profiles differ from the paper main terms by at most $E$ times the source single and pair weights at exponents one. Assume $|F(t_r)|\le C_F$, $|K(t_r,t_s)|\le C_{\rm prod}t_rt_s$, $r\sum_s|\operatorname{Cov}(v_r,v_s)-\operatorname{Cov}(I_r,I_s)|\le R$, and every nuisance-valuation covariance has absolute value at most $C_m/r$. Put $d=\#\{\text{nuisance coordinates}\}$, $J=\operatorname{pairCovarianceScale}(E)$, and $A_2=(1/\rho(U_D)+2E)^2+C_{\rm prod}$, where $U_D$ is the fixed Dickman parameter. For each raw band-gauge vector $q$ and band prime $p$,
--
--   $$|\operatorname{Cov}_{\mu_\xi}(v_p,\operatorname{Res}_{\rm nuis}Q_q)|\le\left[C_{\rm prod}K_0+C_F+4JH+2E+\frac{A_2}{W}+R+\frac{dC_m^2H}{\gamma}\right]\frac{\|q\|}{p}.$$
--
--   Here $Q_q$ is the full band-regression score and the component weights are the source-defined prime-power chamber weights.
--
--   Every input is a finite profile, covariance, or spectral estimate; the result supplies the full nuisance-residual marked row.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperActualFastMarkedRowProfiles.lean#L415-L665

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidual_bandRegression_markedRow_le_of_profiles :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B) {gamma : Real}
  (hgamma : LT.lt.{0} (0 : Real) gamma)
  (hgap :
    ∀ (z : Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B),
      LE.le.{0} (HMul.hMul.{0, 0, 0} gamma (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} z) (2 : Nat)))
        (Inner.inner.{0, u_1} Real z
          ((Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCovarianceOperator.{u_1, u_2} B xi :
              Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B →
                Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B)
            z)))
  (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)) {H K Eprofile CF Cprod R Cmarked : Real},
  LE.le.{0} (0 : Real) H →
    LE.le.{0} (0 : Real) Cmarked →
      LE.le.{0} (0 : Real) Eprofile →
        LE.le.{0} (0 : Real) Cprod →
          LT.lt.{0} (0 : Nat)
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
            LE.le.{0} (∑ j : Band, Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B j) H →
              LE.le.{0}
                  (Erdos390.Full.PrimeSums.bandTReciprocalSum
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                  K →
                (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (p : Nat),
                    Membership.mem.{0, 0}
                        (Erdos390.Full.ArithmeticModel.primeBand
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                        p →
                      ∀ (r : Nat),
                        Membership.mem.{0, 0}
                            (Finset.erase.{0}
                              (Erdos390.Full.ArithmeticModel.primeBand
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                              p)
                            r →
                          LE.le.{0}
                            (abs.{0}
                              (HSub.hSub.{0, 0, 0}
                                (Erdos390.Full.FiniteProbability.expect.{0}
                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1, u_2} B xi
                                      c))
                                  fun
                                    (omega :
                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) c) =>
                                  Erdos390.Full.ArithmeticModel.divInd
                                    (Erdos390.Full.OmittedTiltPairChamber.pairPower p r (1 : Nat) (1 : Nat))
                                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1, u_2} B
                                        xi c)
                                      omega))
                                (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                  (Erdos390.Full.OmittedTiltPairChamber.pairPower p r (1 : Nat) (1 : Nat)))))
                            (HMul.hMul.{0, 0, 0} Eprofile
                              (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p r (1 : Nat) (1 : Nat)))) →
                  (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (p : Nat),
                      Membership.mem.{0, 0}
                          (Erdos390.Full.ArithmeticModel.primeBand
                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                          p →
                        LE.le.{0}
                          (abs.{0}
                            (HSub.hSub.{0, 0, 0}
                              (Erdos390.Full.FiniteProbability.expect.{0}
                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1, u_2} B xi
                                    c))
                                fun
                                  (omega :
                                    Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) c) =>
                                Erdos390.Full.ArithmeticModel.divInd p
                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1, u_2} B xi
                                      c)
                                    omega))
                              (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                p)))
                          (HMul.hMul.{0, 0, 0} Eprofile
                            (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat)))) →
                    (∀
                        (r :
                          Erdos390.Full.ArithmeticBandGeometry.BandPrime
                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                        LE.le.{0}
                          (abs.{0}
                            (Erdos390.Full.DickmanBasic.F
                              (Erdos390.Full.ArithmeticModel.tPrime
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                (↑r : Nat))))
                          CF) →
                      (∀
                          (r s :
                            Erdos390.Full.ArithmeticBandGeometry.BandPrime
                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                          LE.le.{0}
                            (abs.{0}
                              (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel
                                (Erdos390.Full.ArithmeticModel.tPrime
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                  (↑r : Nat))
                                (Erdos390.Full.ArithmeticModel.tPrime
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                  (↑s : Nat))))
                            (HMul.hMul.{0, 0, 0}
                              (HMul.hMul.{0, 0, 0} Cprod
                                (Erdos390.Full.ArithmeticModel.tPrime
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                  (↑r : Nat)))
                              (Erdos390.Full.ArithmeticModel.tPrime
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                (↑s : Nat)))) →
                        (∀
                            (r :
                              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                            LE.le.{0}
                              (HMul.hMul.{0, 0, 0} (↑(↑r : Nat) : Real)
                                (∑ s :
                                  Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                                  abs.{0}
                                    (HSub.hSub.{0, 0, 0}
                                      (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi)
                                        (↑r : Nat) (↑s : Nat))
                                      (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi)
                                        (↑r : Nat) (↑s : Nat)))))
                              R) →
                          (∀
                              (c :
                                Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} B))
                              (r :
                                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                              LE.le.{0}
                                (abs.{0}
                                  (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B xi)
                                    (fun
                                        (m :
                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) =>
                                      WithLp.ofLp.{u_1}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceStatistic.{u_1, u_2} B m) c)
                                    fun
                                      (m :
                                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) =>
                                    Erdos390.Full.ArithmeticModel.valuation (↑r : Nat)
                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) m)))
                                (HMul.hMul.{0, 0, 0} Cmarked (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑(↑r : Nat) : Real)))) →
                            ∀ {p : Nat},
                              Membership.mem.{0, 0}
                                  (Erdos390.Full.ArithmeticModel.primeBand
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                  p →
                                LE.le.{0}
                                  (abs.{0}
                                    (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B xi)
                                      (fun
                                          (m :
                                            Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) =>
                                        Erdos390.Full.ArithmeticModel.valuation p
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) m))
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidualScore.{u_1, u_2} B xi
                                        hgamma hgap
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.bandRegressionScore.{u_1, u_2} B q))))
                                  (HMul.hMul.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0}
                                      (HAdd.hAdd.{0, 0, 0}
                                        (HAdd.hAdd.{0, 0, 0}
                                          (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} Cprod K) CF)
                                            (HAdd.hAdd.{0, 0, 0}
                                              (HAdd.hAdd.{0, 0, 0}
                                                (HMul.hMul.{0, 0, 0}
                                                  (HMul.hMul.{0, 0, 0} (4 : Real)
                                                    (Erdos390.Full.PaperPrimePowerChamberError.pairCovarianceScale
                                                      Eprofile))
                                                  H)
                                                (HMul.hMul.{0, 0, 0} (2 : Real) Eprofile))
                                              (HMul.hMul.{0, 0, 0}
                                                (HAdd.hAdd.{0, 0, 0}
                                                  (HPow.hPow.{0, 0, 0}
                                                    (HAdd.hAdd.{0, 0, 0}
                                                      (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                        (Erdos390.Full.DickmanBasic.rho Erdos390.Full.DickmanBasic.U))
                                                      (HMul.hMul.{0, 0, 0} (2 : Real) Eprofile))
                                                    (2 : Nat))
                                                  Cprod)
                                                (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                  (↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          B)) :
                                                    Real)))))
                                          R)
                                        (HMul.hMul.{0, 0, 0}
                                          (HDiv.hDiv.{0, 0, 0}
                                            (HMul.hMul.{0, 0, 0}
                                              (Real.sqrt
                                                (↑(Fintype.card.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2}
                                                          B))) :
                                                  Real))
                                              (HMul.hMul.{0, 0, 0} Cmarked H))
                                            gamma)
                                          (HMul.hMul.{0, 0, 0}
                                            (Real.sqrt
                                              (↑(Fintype.card.{u_1}
                                                    (Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2}
                                                        B))) :
                                                Real))
                                            Cmarked)))
                                      (Norm.norm.{u_2} q))
                                    (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑p : Real))) := by sorry
