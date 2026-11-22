-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_actualSquarefree_relative_lower_canonicalKappa_of_varianceFactor
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.actualSquarefree_relative_lower_canonicalKappa_of_varianceFactor
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:50:47.986491+00:00
-- url     : https://prove2.me/theorems/44e588d7-5103-4c5d-9c36-8b3282d696fc
-- title:
--   Squarefree slow-variance lower bound with an explicit variance factor
-- statement:
--   Let B have nonempty finite head and band types, ξ a tilt and q a raw-gauge vector. Let C,K,w,v,rowError,Eprofile,CKernel≥0, W>0. Assume ‖q‖sharp≤Cw, ∑t_p/p≤K, |dev_p|≤w, L₁(dev)≤7w, vw²≤V≤4w² and V≤centerEnergy. Suppose an interior prime anchor (t_p∈[1/8,7/8]) has positive weighted mass at least anchorFloor, reference residual rows are bounded by rowError·t_p, single and distinct-pair divisibility profiles have their stated weighted errors Eprofile, and the covariance kernel has magnitude at most CKernel. Then the post-band squarefree variance has the explicit lower bound below. The named coefficient is the source-defined paperScaleSquarefreeSlowConstant, with the listed arguments.
--
--   $$\operatorname{paperScaleSquarefreeSlowConstant}(v,\mathrm{anchorFloor},\mathrm{rowError},E_{\rm profile},C_{\rm Kernel},C,K,1/W)w^2\le\operatorname{Var}_\xi(S_{\rm sf}(q)).$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperActualLemma86PaperScale.lean#L68-L203

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

theorem Erdos390.Full.PaperBridgeFit.BridgeData.actualSquarefree_relative_lower_canonicalKappa_of_varianceFactor :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  [Nonempty.{u_2 + 1} Band] (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
  {C K w varianceFactor rowError Eprofile CKernel anchorFloor : Real},
  LE.le.{0} (0 : Real) C →
    LE.le.{0} (0 : Real) K →
      LE.le.{0} (0 : Real) w →
        LE.le.{0} (0 : Real) varianceFactor →
          LE.le.{0} (0 : Real) rowError →
            LE.le.{0} (0 : Real) Eprofile →
              LE.le.{0} (0 : Real) CKernel →
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
                        q)
                      (HMul.hMul.{0, 0, 0} C w) →
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
                            w) →
                        LE.le.{0}
                            (Erdos390.Full.ArithmeticBandGeometry.Partition.totalL1.{u_2}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                            (HMul.hMul.{0, 0, 0} (7 : Real) w) →
                          LE.le.{0} (HMul.hMul.{0, 0, 0} varianceFactor (HPow.hPow.{0, 0, 0} w (2 : Nat)))
                              (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{u_2}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)) →
                            LE.le.{0}
                                (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{u_2}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                (HMul.hMul.{0, 0, 0} (4 : Real) (HPow.hPow.{0, 0, 0} w (2 : Nat))) →
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
                                          (Set.Icc.{0} (1 / 8 : Real) (HSub.hSub.{0, 0, 0} (1 : Real) (1 / 8 : Real)))
                                          (Erdos390.Full.ArithmeticModel.tPrime
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                            ↑p)) →
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
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
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
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                                  ↑p))) →
                                          (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) (p : Nat),
                                              Membership.mem.{0, 0}
                                                  (Erdos390.Full.ArithmeticModel.primeBand
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
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
                                                            fun omega =>
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
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          B))
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
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
                                                          fun omega =>
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
                                                  (p r :
                                                    Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          B))
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                          B))),
                                                  LE.le.{0}
                                                    (abs.{0}
                                                      (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel
                                                        (Erdos390.Full.ArithmeticModel.tPrime
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B))
                                                          ↑p)
                                                        (Erdos390.Full.ArithmeticModel.tPrime
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B))
                                                          ↑r)))
                                                    CKernel) →
                                                LE.le.{0}
                                                  (HMul.hMul.{0, 0, 0}
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.paperScaleSquarefreeSlowConstant
                                                      varianceFactor anchorFloor rowError Eprofile CKernel C K
                                                      (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                        ↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                u_2}
                                                              B))))
                                                    (HPow.hPow.{0, 0, 0} w (2 : Nat)))
                                                  (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B xi)
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.postBandSquarefreeScore.{u_1,
                                                        u_2}
                                                      B q)
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.postBandSquarefreeScore.{u_1,
                                                        u_2}
                                                      B q)) := by sorry
