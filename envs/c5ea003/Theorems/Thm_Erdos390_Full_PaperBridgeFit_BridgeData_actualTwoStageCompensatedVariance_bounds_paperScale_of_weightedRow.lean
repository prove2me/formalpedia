-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_actualTwoStageCompensatedVariance_bounds_paperScale_of_weightedRow
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.actualTwoStageCompensatedVariance_bounds_paperScale_of_weightedRow
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:20:13.60372+00:00
-- url     : https://prove2.me/theorems/fa385d68-7cf9-4774-bd11-a3776fe4f095
-- title:
--   Two-sided finite compensated variance at the paper scale
-- statement:
--   Let B, ξ and a raw-band equivalence e be given, with nuisance covariance gap γ>0. Let q be the actual band regression defined using e. Assume nonnegative constants C,K,R,v,rowError,Eprofile,CF,CKernel,Cmarked, W>0; ‖q‖sharp≤Cw; the bounds ∑t_p/p≤K, |dev_p|≤w, L₁(dev)≤7w, vw²≤V≤4w² and V≤centerEnergy, with w=B.w; an anchor with t_p∈[1/8,7/8] having positive prime-weight mass at least anchorFloor; reference residual rows bounded by rowError·t_p; the single/pair weighted profile bounds; |F(t_p)|≤CF and |K(t_p,t_q)|≤CKernel. Also assume p∑q|covVV−covII|(p,q)≤R and every nuisance/valuation covariance has magnitude at most Cmarked/p. The literal two-stage compensated variance V₂ satisfies the following inequalities, using the source-defined lower and upper constants with exactly these parameters.
--
--   $$\operatorname{paperScaleLemma86SlowConstantOfRow}(v,\mathrm{anchorFloor},\mathrm{rowError},E_{\rm profile},C_{\rm Kernel},C,K,1/W,R,C_{\rm marked},\gamma)w^2\le V_2\le\operatorname{paperScaleLemma86SlowUpperConstantOfRow}(E_{\rm profile},C_F,C_{\rm Kernel},C,K,1/W,R)w^2.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperActualLemma86PaperScale.lean#L298-L470

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

theorem Erdos390.Full.PaperBridgeFit.BridgeData.actualTwoStageCompensatedVariance_bounds_paperScale_of_weightedRow :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  [inst_5 : Nonempty.{u_2 + 1} Band] (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  {gamma : Real} (hgamma : LT.lt.{0} (0 : Real) gamma)
  (hgap :
    ∀ (z : Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B),
      LE.le.{0} (HMul.hMul.{0, 0, 0} gamma (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} z) (2 : Nat)))
        (Inner.inner.{0, u_1} Real z
          ((Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCovarianceOperator.{u_1, u_2} B xi :
              Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B →
                Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, u_2} B)
            z)))
  (e :
    LinearEquiv.{0, 0, u_2, u_2} (RingHom.id.{0} Real)
      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)
      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
  {C K R varianceFactor rowError Eprofile CF CKernel anchorFloor Cmarked : Real},
  LE.le.{0} (0 : Real) C →
    LE.le.{0} (0 : Real) K →
      LE.le.{0} (0 : Real) R →
        LE.le.{0} (0 : Real) varianceFactor →
          LE.le.{0} (0 : Real) rowError →
            LE.le.{0} (0 : Real) Eprofile →
              LE.le.{0} (0 : Real) CF →
                LE.le.{0} (0 : Real) CKernel →
                  LE.le.{0} (0 : Real) Cmarked →
                    LT.lt.{0} (0 : Nat)
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
                      LE.le.{0}
                          (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                            (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                            (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                              (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                            (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1, u_2} B xi hgamma hgap
                              e))
                          (HMul.hMul.{0, 0, 0} C (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)) →
                        LE.le.{0}
                            (Erdos390.Full.PrimeSums.bandTReciprocalSum
                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                            K →
                          (∀
                              (p :
                                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                              LE.le.{0}
                                (abs.{0}
                                  (Erdos390.Full.ArithmeticBandGeometry.Partition.deviation.{u_2}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B) p))
                                (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)) →
                            LE.le.{0}
                                (Erdos390.Full.ArithmeticBandGeometry.Partition.totalL1.{u_2}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                (HMul.hMul.{0, 0, 0} (7 : Real)
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)) →
                              LE.le.{0}
                                  (HMul.hMul.{0, 0, 0} varianceFactor
                                    (HPow.hPow.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)
                                      (2 : Nat)))
                                  (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{u_2}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)) →
                                LE.le.{0}
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                    (HMul.hMul.{0, 0, 0} (4 : Real)
                                      (HPow.hPow.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2} B)
                                        (2 : Nat))) →
                                  LE.le.{0}
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.centerEnergy.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)) →
                                    ∀
                                      (anchor :
                                        Finset.{0}
                                          (Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))),
                                      (∀
                                          (p :
                                            Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                                          Membership.mem.{0, 0} anchor p →
                                            Membership.mem.{0, 0}
                                              (Set.Icc.{0} (1 / 8 : Real)
                                                (HSub.hSub.{0, 0, 0} (1 : Real) (1 / 8 : Real)))
                                              (Erdos390.Full.ArithmeticModel.tPrime
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                (↑p : Nat))) →
                                        LT.lt.{0} (0 : Real)
                                            (Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass.{0}
                                              (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                              anchor) →
                                          LE.le.{0} anchorFloor
                                              (Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass.{0}
                                                (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                                anchor) →
                                            (∀
                                                (p :
                                                  Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                        B))),
                                                LE.le.{0}
                                                  (abs.{0}
                                                    (Erdos390.Full.FiniteAnchoredDirichletQuadratic.rowResidual.{0}
                                                      (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                            B)))
                                                      (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeDiagonal
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                            B)))
                                                      (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeKernel
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                            B)))
                                                      p))
                                                  (HMul.hMul.{0, 0, 0} rowError
                                                    (Erdos390.Full.ArithmeticModel.tPrime
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          B))
                                                      (↑p : Nat)))) →
                                              (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (p : Nat),
                                                  Membership.mem.{0, 0}
                                                      (Erdos390.Full.ArithmeticModel.primeBand
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                            B))
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                            B)))
                                                      p →
                                                    ∀ (r : Nat),
                                                      Membership.mem.{0, 0}
                                                          (Finset.erase.{0}
                                                            (Erdos390.Full.ArithmeticModel.primeBand
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B))
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B)))
                                                            p)
                                                          r →
                                                        LE.le.{0}
                                                          (abs.{0}
                                                            (HSub.hSub.{0, 0, 0}
                                                              (Erdos390.Full.FiniteProbability.expect.{0}
                                                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                                      u_2}
                                                                    B xi c))
                                                                fun
                                                                  (omega :
                                                                    Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1}
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                          u_2}
                                                                        B)
                                                                      c) =>
                                                                Erdos390.Full.ArithmeticModel.divInd
                                                                  (Erdos390.Full.OmittedTiltPairChamber.pairPower p r
                                                                    (1 : Nat) (1 : Nat))
                                                                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0}
                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                                        u_2}
                                                                      B xi c)
                                                                    omega))
                                                              (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                      u_2}
                                                                    B))
                                                                (Erdos390.Full.OmittedTiltPairChamber.pairPower p r
                                                                  (1 : Nat) (1 : Nat)))))
                                                          (HMul.hMul.{0, 0, 0} Eprofile
                                                            (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p r
                                                              (1 : Nat) (1 : Nat)))) →
                                                (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (p : Nat),
                                                    Membership.mem.{0, 0}
                                                        (Erdos390.Full.ArithmeticModel.primeBand
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B))
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B)))
                                                        p →
                                                      LE.le.{0}
                                                        (abs.{0}
                                                          (HSub.hSub.{0, 0, 0}
                                                            (Erdos390.Full.FiniteProbability.expect.{0}
                                                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                                    u_2}
                                                                  B xi c))
                                                              fun
                                                                (omega :
                                                                  Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1}
                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                        u_2}
                                                                      B)
                                                                    c) =>
                                                              Erdos390.Full.ArithmeticModel.divInd p
                                                                (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                                      u_2}
                                                                    B xi c)
                                                                  omega))
                                                            (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B))
                                                              p)))
                                                        (HMul.hMul.{0, 0, 0} Eprofile
                                                          (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p
                                                            (1 : Nat)))) →
                                                  (∀
                                                      (p :
                                                        Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B))
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B))),
                                                      LE.le.{0}
                                                        (abs.{0}
                                                          (Erdos390.Full.DickmanBasic.F
                                                            (Erdos390.Full.ArithmeticModel.tPrime
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B))
                                                              (↑p : Nat))))
                                                        CF) →
                                                    (∀
                                                        (p r :
                                                          Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                  u_2}
                                                                B))
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                  u_2}
                                                                B))),
                                                        LE.le.{0}
                                                          (abs.{0}
                                                            (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel
                                                              (Erdos390.Full.ArithmeticModel.tPrime
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                      u_2}
                                                                    B))
                                                                (↑p : Nat))
                                                              (Erdos390.Full.ArithmeticModel.tPrime
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                      u_2}
                                                                    B))
                                                                (↑r : Nat))))
                                                          CKernel) →
                                                      (∀
                                                          (p :
                                                            Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B))
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B))),
                                                          LE.le.{0}
                                                            (HMul.hMul.{0, 0, 0} (↑(↑p : Nat) : Real)
                                                              (∑ r :
                                                                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                        u_2}
                                                                      B))
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                        u_2}
                                                                      B)),
                                                                abs.{0}
                                                                  (HSub.hSub.{0, 0, 0}
                                                                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1,
                                                                          u_2}
                                                                        B xi)
                                                                      (↑p : Nat) (↑r : Nat))
                                                                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1,
                                                                          u_2}
                                                                        B xi)
                                                                      (↑p : Nat) (↑r : Nat)))))
                                                            R) →
                                                        (∀
                                                            (c :
                                                              Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1,
                                                                    u_2}
                                                                  B))
                                                            (p :
                                                              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                      u_2}
                                                                    B))
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                      u_2}
                                                                    B))),
                                                            LE.le.{0}
                                                              (abs.{0}
                                                                (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1,
                                                                      u_2}
                                                                    B xi)
                                                                  (fun
                                                                      (m :
                                                                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                              u_2}
                                                                            B)) =>
                                                                    WithLp.ofLp.{u_1}
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceStatistic.{u_1,
                                                                          u_2}
                                                                        B m)
                                                                      c)
                                                                  fun
                                                                    (m :
                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                            u_2}
                                                                          B)) =>
                                                                  Erdos390.Full.ArithmeticModel.valuation (↑p : Nat)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                          u_2}
                                                                        B)
                                                                      m)))
                                                              (HMul.hMul.{0, 0, 0} Cmarked
                                                                (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                  (↑(↑p : Nat) : Real)))) →
                                                          And
                                                            (LE.le.{0}
                                                              (HMul.hMul.{0, 0, 0}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.paperScaleLemma86SlowConstantOfRow.{u_1,
                                                                    u_2}
                                                                  B varianceFactor anchorFloor rowError Eprofile CKernel
                                                                  C K
                                                                  (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                    (↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                              u_2}
                                                                            B)) :
                                                                      Real))
                                                                  R Cmarked gamma)
                                                                (HPow.hPow.{0, 0, 0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2}
                                                                    B)
                                                                  (2 : Nat)))
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.actualTwoStageCompensatedVariance.{u_1,
                                                                  u_2}
                                                                B xi hgamma hgap e))
                                                            (LE.le.{0}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.actualTwoStageCompensatedVariance.{u_1,
                                                                  u_2}
                                                                B xi hgamma hgap e)
                                                              (HMul.hMul.{0, 0, 0}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.paperScaleLemma86SlowUpperConstantOfRow
                                                                  Eprofile CF CKernel C K
                                                                  (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                    (↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                              u_2}
                                                                            B)) :
                                                                      Real))
                                                                  R)
                                                                (HPow.hPow.{0, 0, 0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, u_2}
                                                                    B)
                                                                  (2 : Nat)))) := by sorry
