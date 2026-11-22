-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_referenceSharpProjectedEquiv_of_primeGraph
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.exists_referenceSharpProjectedEquiv_of_primeGraph
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:18:05.223848+00:00
-- url     : https://prove2.me/theorems/85eb1354-d109-43b8-945a-e359195099b1
-- title:
--   Stable inversion of the reference sharp operator via the prime graph
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. Let $B$ be a bridge with finite head and band sets, and write $t_p=\log p/\log y_n$, $h_i$ for harmonic band masses, $\alpha_i$ for band centers, and $j(p)$ for the band of $p$. Let $R_{pr}$ be its squarefree Poisson–Dickman reference entry, $I_p=\mathbf1_{p\mid m}$, and $\mu_\xi$ its tilted law. Write $d_p=\alpha_{j(p)}-t_p$ for the prime deviation. Fix an interval certificate for the partition and an anchor set of band primes with $t_p\in[1/8,7/8]$ and positive source anchor mass $m$. Let $r,w,C_F,C_K\ge0$. Assume the prime row residual is bounded by $rt_p$, $|F(t_p)-F(\alpha_{j(p)})|\le C_F|d_p|$, $|K(t_p,t_q)|\le C_Kt_p$, $|d_p|\le w$, and $\sum_p|d_p|/p\le7w$. Put $A=4/(\kappa_{\rm slow}m)$ and $e=r+(2C_F+7C_K)w$, where $\kappa_{\rm slow}$ is the source canonical slow-gap constant. If $2Ae<1$, the projected reference sharp operator $T$ determined by the certificate is a continuous linear equivalence on the sharp gauge space, and
--
--   $$\|T^{-1}v\|\le\frac A{1-2Ae}\|v\|.$$
--
--   The estimate depends on the anchor mass and arithmetic errors, without an explicit number-of-bands or minimum-center loss.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperReferenceSharpPrimeGraph.lean#L920-L1086

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

theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_referenceSharpProjectedEquiv_of_primeGraph :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band)
  (cert :
    Erdos390.Full.PositiveCellTransfer.IntervalCertificate.{u_2}
      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
  (anchor :
    Finset.{0}
      (Erdos390.Full.ArithmeticBandGeometry.BandPrime
        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))),
  (∀
      (q :
        Erdos390.Full.ArithmeticBandGeometry.BandPrime
          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
      Membership.mem.{0, 0} anchor q →
        Membership.mem.{0, 0} (Set.Icc.{0} (1 / 8 : Real) (HSub.hSub.{0, 0, 0} (1 : Real) (1 / 8 : Real)))
          (Erdos390.Full.ArithmeticModel.tPrime
            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
            (↑q : Nat))) →
    ∀ {rowError w CF CKernel : Real},
      LE.le.{0} (0 : Real) rowError →
        LE.le.{0} (0 : Real) w →
          LE.le.{0} (0 : Real) CF →
            LE.le.{0} (0 : Real) CKernel →
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
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                        (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeDiagonal
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                        (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeKernel
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                        p))
                    (HMul.hMul.{0, 0, 0} rowError
                      (Erdos390.Full.ArithmeticModel.tPrime
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                        (↑p : Nat)))) →
                (∀
                    (p :
                      Erdos390.Full.ArithmeticBandGeometry.BandPrime
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                    LE.le.{0}
                      (abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.DickmanBasic.F
                            (Erdos390.Full.ArithmeticModel.tPrime
                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                              (↑p : Nat)))
                          (Erdos390.Full.DickmanBasic.F
                            (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B
                              (Erdos390.Full.ArithmeticBandGeometry.Partition.band.{u_2}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B) p)))))
                      (HMul.hMul.{0, 0, 0} CF
                        (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviation.{u_1, u_2} B p)))) →
                  (∀
                      (p q :
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
                              (↑p : Nat))
                            (Erdos390.Full.ArithmeticModel.tPrime
                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                              (↑q : Nat))))
                        (HMul.hMul.{0, 0, 0} CKernel
                          (Erdos390.Full.ArithmeticModel.tPrime
                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                            (↑p : Nat)))) →
                    (∀
                        (p :
                          Erdos390.Full.ArithmeticBandGeometry.BandPrime
                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                        LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviation.{u_1, u_2} B p)) w) →
                      LE.le.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.primeDeviationL1.{u_1, u_2} B)
                          (HMul.hMul.{0, 0, 0} (7 : Real) w) →
                        LT.lt.{0} (0 : Real)
                            (Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass.{0}
                              (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                              anchor) →
                          LT.lt.{0}
                              (HMul.hMul.{0, 0, 0}
                                (HDiv.hDiv.{0, 0, 0} (4 : Real)
                                  (HMul.hMul.{0, 0, 0} Erdos390.Full.PaperCanonicalSlowKappa.canonicalSlowKappa
                                    (Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass.{0}
                                      (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                      anchor)))
                                (HMul.hMul.{0, 0, 0} (2 : Real)
                                  (HAdd.hAdd.{0, 0, 0} rowError
                                    (HMul.hMul.{0, 0, 0}
                                      (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) CF)
                                        (HMul.hMul.{0, 0, 0} (7 : Real) CKernel))
                                      w))))
                              (1 : Real) →
                            ∃ (referenceEquiv :
                              ContinuousLinearEquiv.{0, 0, u_2, u_2} (RingHom.id.{0} Real)
                                ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))
                                ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))),
                              And
                                (∀
                                  (q :
                                    ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                        (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                        (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))),
                                  Eq.{u_2 + 1}
                                    ((referenceEquiv :
                                        ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))) →
                                          ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))))
                                      q)
                                    ((Erdos390.Full.ArithmeticGaugeStableInverse.projectedSharpCLM.{u_2}
                                          (Erdos390.Full.CompressedArithmeticOperator.arithmeticDiagonal.{u_2}
                                            (Erdos390.Full.ArithmeticModel.y
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                            (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_2} cert)
                                            (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_2} cert))
                                          (Erdos390.Full.CompressedArithmeticOperator.arithmeticKernel.{u_2}
                                            (Erdos390.Full.ArithmeticModel.y
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                            (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_2} cert)
                                            (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_2} cert))
                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                          (Erdos390.Full.MovingLowGaugeTransfer.sharpWeight.{u_2}
                                            (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                            (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))
                                          (ne_of_gt.{0}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.actualSharpWeightTotal_pos.{u_1,
                                                u_2}
                                              B)) :
                                        ↥(Erdos390.Full.FiniteGraphStableInverse.GaugeSpace.{u_2}
                                              (Erdos390.Full.MovingLowGaugeTransfer.sharpWeight.{u_2}
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))) →
                                          ↥(Erdos390.Full.FiniteGraphStableInverse.GaugeSpace.{u_2}
                                              (Erdos390.Full.MovingLowGaugeTransfer.sharpWeight.{u_2}
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))))
                                      q))
                                (∀
                                  (v :
                                    ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                        (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                        (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))),
                                  LE.le.{0}
                                    (Norm.norm.{u_2}
                                      ((ContinuousLinearEquiv.symm.{0, 0, u_2, u_2} referenceEquiv :
                                          ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))) →
                                            ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))))
                                        v))
                                    (HMul.hMul.{0, 0, 0}
                                      (HDiv.hDiv.{0, 0, 0}
                                        (HDiv.hDiv.{0, 0, 0} (4 : Real)
                                          (HMul.hMul.{0, 0, 0} Erdos390.Full.PaperCanonicalSlowKappa.canonicalSlowKappa
                                            (Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass.{0}
                                              (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                              anchor)))
                                        (HSub.hSub.{0, 0, 0} (1 : Real)
                                          (HMul.hMul.{0, 0, 0}
                                            (HDiv.hDiv.{0, 0, 0} (4 : Real)
                                              (HMul.hMul.{0, 0, 0}
                                                Erdos390.Full.PaperCanonicalSlowKappa.canonicalSlowKappa
                                                (Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass.{0}
                                                  (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                        B)))
                                                  anchor)))
                                            (HMul.hMul.{0, 0, 0} (2 : Real)
                                              (HAdd.hAdd.{0, 0, 0} rowError
                                                (HMul.hMul.{0, 0, 0}
                                                  (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) CF)
                                                    (HMul.hMul.{0, 0, 0} (7 : Real) CKernel))
                                                  w))))))
                                      (Norm.norm.{u_2} v))) := by sorry
