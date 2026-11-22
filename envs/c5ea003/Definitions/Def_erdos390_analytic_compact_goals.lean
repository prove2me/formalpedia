-- Prove2me | Definitions.Def_erdos390_analytic_compact_goals
-- name    : erdos390_analytic_compact_goals
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T15:53:12.531014+00:00
-- url     : https://prove2.me/theorems/9c41af92-9cfb-4862-ae39-cdbfbce5cc21
-- title:
--   Explicit propositions for four analytic comparison estimates
-- statement:
--   This file names four fully quantified analytic propositions: the many-low ordinary inverse bound, the uniform actual-band Schur equivalence and quadratic bound, and two power-correction comparison estimates. Each name expands definitionally to the original quantified proposition, with all hypotheses and universe parameters retained. The definitions assert no new axioms.
-- source:
--   https://github.com/ShouqiaoW/erdos/tree/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean

import Definitions.Def_erdos390_analytic_foundations_001
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_analytic_statement_auxiliaries
import Definitions.Def_erdos390_dickman_step_function
import Definitions.Def_erdos390_source_bank_interface
import Mathlib
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_MediumPNT

universe u_1 u_2 u_3 u_4
set_option maxRecDepth 10000
set_option maxHeartbeats 0

noncomputable def Erdos390.AnalyticCompactGoal001 : Prop :=
∀ {Band : Type u_1} {Low : Type u_2} {High : Type u_3} [inst : Fintype.{u_1} Band] [inst_1 : Fintype.{u_2} Low]
  [inst_2 : Fintype.{u_3} High] {epsilon : Real} (M : Erdos390.Full.ContinuumCellGraph.IntervalMesh.{u_1} epsilon Band)
  [inst_3 : DecidableEq.{u_1 + 1} Band] [inst_4 : Nonempty.{u_1 + 1} Band] [Nonempty.{u_3 + 1} High]
  (e : Equiv.{max (u_3 + 1) (u_2 + 1), u_1 + 1} (Sum.{u_2, u_3} Low High) Band) (diagonalA : Band → Real)
  (kernelA : Band → Band → Real) (H alphaA : Band → Real)
  {C kappa amin amax alphaAMax lowCenter lowLength totalLength gaugeRatio d residual rowError R rho : Real},
  LE.le.{0} (0 : Real) C →
    (∀ (s : Real),
        Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) s →
          ∀ (t : Real),
            Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) t →
              LE.le.{0} (abs.{0} (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel s t))
                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C s) t)) →
      LT.lt.{0} (0 : Real) kappa →
        (∀ (s : Real),
            Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) s →
              ∀ (t : Real),
                Membership.mem.{0, 0} (Set.Icc.{0} epsilon (HSub.hSub.{0, 0, 0} (1 : Real) epsilon)) t →
                  LE.le.{0} kappa (Neg.neg.{0} (Erdos390.Full.ConditionedPoissonLimit.covarianceKernelQuotient t s))) →
          LT.lt.{0} (0 : Real)
              (∑ i, Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitHighAnchor.{u_1, u_2, u_3} M e i) →
            LT.lt.{0} (0 : Real) amin →
              (∀ (i : High),
                  LE.le.{0} amin
                    (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e (Sum.inr.{u_2, u_3} i)))) →
                (∀ (i : High),
                    LE.le.{0} (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e (Sum.inr.{u_2, u_3} i)))
                      amax) →
                  LE.le.{0} (0 : Real) amax →
                    LE.le.{0} (0 : Real) lowCenter →
                      (∀ (l : Low),
                          LE.le.{0}
                            (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e (Sum.inl.{u_2, u_3} l)))
                            lowCenter) →
                        LE.le.{0} (0 : Real) lowLength →
                          LE.le.{0}
                              (∑ l,
                                Erdos390.Full.ContinuumCellGraph.IntervalMesh.length.{u_1} M (e (Sum.inl.{u_2, u_3} l)))
                              lowLength →
                            LE.le.{0} (0 : Real) totalLength →
                              LE.le.{0} (∑ i, Erdos390.Full.ContinuumCellGraph.IntervalMesh.length.{u_1} M i)
                                  totalLength →
                                ∀ (hH : ∀ (i : Band), LT.lt.{0} (0 : Real) (H i))
                                  (hAlphaA : ∀ (i : Band), LT.lt.{0} (0 : Real) (alphaA i)),
                                  (∀ (i : Band), LE.le.{0} (alphaA i) alphaAMax) →
                                    LE.le.{0}
                                        (∑ l,
                                          HMul.hMul.{0, 0, 0} (H (e (Sum.inl.{u_2, u_3} l)))
                                            (alphaA (e (Sum.inl.{u_2, u_3} l))))
                                        (HMul.hMul.{0, 0, 0} gaugeRatio
                                          (∑ i,
                                            HMul.hMul.{0, 0, 0}
                                              (HMul.hMul.{0, 0, 0} (H (e (Sum.inr.{u_2, u_3} i)))
                                                (alphaA (e (Sum.inr.{u_2, u_3} i))))
                                              (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M
                                                (e (Sum.inr.{u_2, u_3} i))))) →
                                      LT.lt.{0} d (1 : Real) →
                                        (∀ (l : Low),
                                            LE.le.{0}
                                              (abs.{0}
                                                (HSub.hSub.{0, 0, 0}
                                                  (Erdos390.Full.ContinuumCellGraph.IntervalMesh.normalizedDiagonalCell.{u_1}
                                                    M (e (Sum.inl.{u_2, u_3} l)))
                                                  (1 : Real)))
                                              d) →
                                          LE.le.{0} (0 : Real) residual →
                                            (∀ (i : Band),
                                                LE.le.{0}
                                                  (abs.{0}
                                                    (Erdos390.Full.ContinuumCellGraph.IntervalMesh.rowResidual.{u_1} M
                                                      i))
                                                  residual) →
                                              LE.le.{0} (0 : Real) rowError →
                                                (∀
                                                    (b :
                                                      ↥(Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{u_1} H
                                                          alphaA))
                                                    (i : Band),
                                                    LE.le.{0}
                                                      (abs.{0}
                                                        (HSub.hSub.{0, 0, 0}
                                                          (Erdos390.Full.PaperWeightedInverseExport.rawOperator.{u_1}
                                                            diagonalA kernelA (↑b) i)
                                                          (Erdos390.Full.PaperWeightedInverseExport.rawOperator.{u_1}
                                                            (Erdos390.Full.ContinuumCellGraph.IntervalMesh.normalizedDiagonalCell.{u_1}
                                                              M)
                                                            (Erdos390.Full.ContinuumCellGraph.IntervalMesh.normalizedKernelCell.{u_1}
                                                              M)
                                                            (↑b) i)))
                                                      (HMul.hMul.{0, 0, 0} rowError (Norm.norm.{u_1} b))) →
                                                  LE.le.{0} (0 : Real) R →
                                                    LE.le.{0}
                                                        (HMul.hMul.{0, 0, 0} alphaAMax
                                                          (∑ i, HMul.hMul.{0, 0, 0} (H i) (alphaA i)))
                                                        (HMul.hMul.{0, 0, 0} R
                                                          (Erdos390.Full.MovingLowGaugeTransfer.sharpWeightTotal.{u_1} H
                                                            alphaA)) →
                                                      LE.le.{0} rho (1 / 2 : Real) →
                                                        LE.le.{0}
                                                            (HMul.hMul.{0, 0, 0} alphaAMax
                                                              (∑ i,
                                                                abs.{0}
                                                                  (HSub.hSub.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0} (H i) (alphaA i))
                                                                    (HMul.hMul.{0, 0, 0}
                                                                      (Erdos390.Full.ContinuumCellGraph.IntervalMesh.harmonicMass.{u_1}
                                                                        M i)
                                                                      (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1}
                                                                        M i)))))
                                                            (HMul.hMul.{0, 0, 0} rho
                                                              (Erdos390.Full.MovingLowGaugeTransfer.sharpWeightTotal.{u_1}
                                                                H alphaA)) →
                                                          (have epsLow :=
                                                              HDiv.hDiv.{0, 0, 0}
                                                                (HAdd.hAdd.{0, 0, 0} residual
                                                                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C lowCenter)
                                                                    totalLength))
                                                                (HSub.hSub.{0, 0, 0} (1 : Real) d);
                                                            LE.le.{0}
                                                              (Max.max.{0} epsLow
                                                                (HMul.hMul.{0, 0, 0} amax
                                                                  (HAdd.hAdd.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0}
                                                                      (HMul.hMul.{0, 0, 0} (2 : Real)
                                                                        (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                          (HMul.hMul.{0, 0, 0} kappa
                                                                            (∑ i,
                                                                              Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitHighAnchor.{u_1,
                                                                                  u_2, u_3}
                                                                                M e i))))
                                                                      (HAdd.hAdd.{0, 0, 0}
                                                                        (HDiv.hDiv.{0, 0, 0}
                                                                          (HMul.hMul.{0, 0, 0}
                                                                            (HMul.hMul.{0, 0, 0} C lowCenter) lowLength)
                                                                          amin)
                                                                        (HMul.hMul.{0, 0, 0}
                                                                          (HMul.hMul.{0, 0, 0} C lowLength) epsLow)))
                                                                    (HMul.hMul.{0, 0, 0} gaugeRatio epsLow))))
                                                              (1 / 2 : Real)) →
                                                            (have Clow :=
                                                                HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                  (HSub.hSub.{0, 0, 0} (1 : Real) d);
                                                              have Cmain :=
                                                                Max.max.{0} Clow
                                                                  (HMul.hMul.{0, 0, 0} amax
                                                                    (HAdd.hAdd.{0, 0, 0}
                                                                      (HMul.hMul.{0, 0, 0}
                                                                        (HMul.hMul.{0, 0, 0} (2 : Real)
                                                                          (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                            (HMul.hMul.{0, 0, 0} kappa
                                                                              (∑ i,
                                                                                Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitHighAnchor.{u_1,
                                                                                    u_2, u_3}
                                                                                  M e i))))
                                                                        (HAdd.hAdd.{0, 0, 0}
                                                                          (HDiv.hDiv.{0, 0, 0} (1 : Real) amin)
                                                                          (HMul.hMul.{0, 0, 0}
                                                                            (HMul.hMul.{0, 0, 0} C lowLength) Clow)))
                                                                      (HMul.hMul.{0, 0, 0} gaugeRatio Clow)));
                                                              LE.le.{0}
                                                                (HMul.hMul.{0, 0, 0}
                                                                  (HMul.hMul.{0, 0, 0} (4 : Real) Cmain)
                                                                  (HMul.hMul.{0, 0, 0}
                                                                    (HAdd.hAdd.{0, 0, 0} (1 : Real) R)
                                                                    (HAdd.hAdd.{0, 0, 0} rowError residual)))
                                                                (1 / 2 : Real)) →
                                                              ∀
                                                                (b :
                                                                  ↥(Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{u_1}
                                                                      H alphaA)),
                                                                LE.le.{0} (Norm.norm.{u_1} b)
                                                                  (HMul.hMul.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0} (8 : Real)
                                                                      (Max.max.{0}
                                                                        (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                          (HSub.hSub.{0, 0, 0} (1 : Real) d))
                                                                        (HMul.hMul.{0, 0, 0} amax
                                                                          (HAdd.hAdd.{0, 0, 0}
                                                                            (HMul.hMul.{0, 0, 0}
                                                                              (HMul.hMul.{0, 0, 0} (2 : Real)
                                                                                (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                                  (HMul.hMul.{0, 0, 0} kappa
                                                                                    (∑ i,
                                                                                      Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitHighAnchor.{u_1,
                                                                                          u_2, u_3}
                                                                                        M e i))))
                                                                              (HAdd.hAdd.{0, 0, 0}
                                                                                (HDiv.hDiv.{0, 0, 0} (1 : Real) amin)
                                                                                (HMul.hMul.{0, 0, 0}
                                                                                  (HMul.hMul.{0, 0, 0} C lowLength)
                                                                                  (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                                    (HSub.hSub.{0, 0, 0} (1 : Real)
                                                                                      d)))))
                                                                            (HMul.hMul.{0, 0, 0} gaugeRatio
                                                                              (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                                (HSub.hSub.{0, 0, 0} (1 : Real) d)))))))
                                                                    (Norm.norm.{u_1}
                                                                      ((Erdos390.Full.PaperWeightedInverseExport.projectedRawLinearMap.{u_1}
                                                                          diagonalA kernelA H alphaA
                                                                          (ne_of_gt.{0}
                                                                            (id.{0}
                                                                              (id.{0}
                                                                                (Finset.sum_pos.{u_1, 0}
                                                                                  (fun i _hi =>
                                                                                    mul_pos.{0} (hH i)
                                                                                      (sq_pos_of_pos.{0} (hAlphaA i)))
                                                                                  Finset.univ_nonempty.{u_1})))))
                                                                        b)))

noncomputable def Erdos390.AnalyticCompactGoal002 : Prop :=
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band] [inst_4 : Nonempty.{u_1 + 1} Head]
  [inst_5 : Nonempty.{u_2 + 1} Band] (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) {U : Real}
  (hU : LE.le.{0} (1 : Real) U)
  (hlowerOne :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma))
  (hupperU :
    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
      LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) U)
  (W : Nat) (hW : LT.lt.{0} (1 : Nat) W) (a : NNReal) (marginFloor centerScale Cfull : Real),
  LT.lt.{0} (0 : Real) marginFloor →
    LT.lt.{0} (0 : Real) centerScale →
      LT.lt.{0} (0 : Real) Cfull →
        ∀ (epsilon : Nat → Real),
          (∀ (n : Nat), LE.le.{0} (0 : Real) (epsilon n)) →
            Filter.Tendsto.{0, 0}
                (fun (n : Nat) => HMul.hMul.{0, 0, 0} (epsilon n) (Real.log (Erdos390.Full.Scale.L n))) Filter.atTop.{0}
                (nhds.{0} (0 : Real)) →
              ∀ᶠ (n : Nat) in Filter.atTop.{0},
                ∀ (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band),
                  Eq.{1}
                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                      n →
                    ∀
                      (hBW :
                        Eq.{1}
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                          W)
                      (T :
                        Erdos390.Full.PaperGuardCensus.BarycentricTarget.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                      LE.le.{0} marginFloor (Erdos390.Full.PaperGuardCensus.BarycentricTarget.cellMassMargin.{u_1} T) →
                        ∀
                          (hbaseline :
                            Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1, u_2} B)
                              (Erdos390.Full.PaperGuardCensus.BarycentricTarget.baseline.{u_1} T))
                          (hlo :
                            ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                              Eq.{1}
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) sigma)
                                (Erdos390.Full.ArithmeticModel.physicalBound
                                  (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
                          (hhi :
                            ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                              Eq.{1}
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) sigma)
                                (Erdos390.Full.ArithmeticModel.physicalBound
                                  (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
                          (fullEquiv :
                            (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) →
                              Membership.mem.{u_1, u_1}
                                  (Metric.closedBall.{u_1}
                                    (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                    (↑a : Real))
                                  z →
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
                          (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                              (hz :
                                Membership.mem.{u_1, u_1}
                                  (Metric.closedBall.{u_1}
                                    (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                    (↑a : Real))
                                  z)
                              (q :
                                ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))),
                              Eq.{u_2 + 1}
                                ((fullEquiv z hz :
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
                                ((Erdos390.Full.PaperBridgeFit.BridgeData.actualFullProjectedCLM.{u_1, u_2} B
                                      ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2} B :
                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B) →
                                            Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                        z) :
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
                                  q)) →
                            (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                (hz :
                                  Membership.mem.{u_1, u_1}
                                    (Metric.closedBall.{u_1}
                                      (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                      (↑a : Real))
                                    z)
                                (v :
                                  ↥(Erdos390.Full.PaperWeightedInverseExport.SharpGaugeSpace.{u_2}
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B))
                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{u_2}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)))),
                                LE.le.{0}
                                  (Norm.norm.{u_2}
                                    ((ContinuousLinearEquiv.symm.{0, 0, u_2, u_2} (fullEquiv z hz) :
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
                                  (HMul.hMul.{0, 0, 0} Cfull (Norm.norm.{u_2} v))) →
                              (∀ (i : Band),
                                  LE.le.{0}
                                    (HDiv.hDiv.{0, 0, 0} centerScale
                                      (Real.log
                                        (Erdos390.Full.Scale.L
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))))
                                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B i)) →
                                (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)),
                                    Membership.mem.{u_1, u_1}
                                        (Metric.closedBall.{u_1}
                                          (0 :
                                            ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                          (↑a : Real))
                                        z →
                                      ∀
                                        (c :
                                          Erdos390.Full.PaperBridgeFit.NuisanceCoord.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} B))
                                        (p :
                                          Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
                                        LE.le.{0}
                                          (abs.{0}
                                            (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B
                                                ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2}
                                                      B :
                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                            u_2}
                                                          B) →
                                                      Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                  z))
                                              (fun
                                                  (m :
                                                    Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                        B)) =>
                                                WithLp.ofLp.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceStatistic.{u_1, u_2}
                                                    B m)
                                                  c)
                                              fun
                                                (m :
                                                  Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2}
                                                      B)) =>
                                              Erdos390.Full.ArithmeticModel.valuation (↑p : Nat)
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) m)))
                                          (HMul.hMul.{0, 0, 0}
                                            (epsilon
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                            (HDiv.hDiv.{0, 0, 0} (1 : Real) (↑(↑p : Nat) : Real)))) →
                                  let gamma :=
                                    Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma.{u_1, u_2} B
                                      I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T;
                                  let rate :=
                                    Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceMarkedSchurRate.{u_1, u_2} B
                                      (epsilon
                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                      gamma
                                      (HDiv.hDiv.{0, 0, 0} centerScale
                                        (Real.log
                                          (Erdos390.Full.Scale.L
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))));
                                  let Cschur :=
                                    HDiv.hDiv.{0, 0, 0} Cfull
                                      (HSub.hSub.{0, 0, 0} (1 : Real)
                                        (HMul.hMul.{0, 0, 0} Cfull (HMul.hMul.{0, 0, 0} (2 : Real) rate)));
                                  ∃ (e :
                                    (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B)) →
                                      Membership.mem.{u_1, u_1}
                                          (Metric.closedBall.{u_1}
                                            (0 :
                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2}
                                                  B))
                                            (↑a : Real))
                                          z →
                                        LinearEquiv.{0, 0, u_2, u_2} (RingHom.id.{0} Real)
                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)
                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                                    And
                                      (∀
                                        (z :
                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                        (hz :
                                          Membership.mem.{u_1, u_1}
                                            (Metric.closedBall.{u_1}
                                              (0 :
                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2}
                                                    B))
                                              (↑a : Real))
                                            z)
                                        (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                                        Eq.{u_2 + 1}
                                          ((e z hz :
                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B) →
                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
                                            q)
                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.actualBandSchurLinearMap.{u_1, u_2}
                                                B
                                                ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, u_2}
                                                      B :
                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                            u_2}
                                                          B) →
                                                      Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                  z)
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                    u_2}
                                                  B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                    u_2}
                                                  B I a hU hlowerOne hupperU hlo hhi T hbaseline
                                                  (Decidable.byContradiction
                                                    fun
                                                      (a :
                                                        Not
                                                          (LT.lt.{0} (1 : Nat)
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                  u_2}
                                                                B)))) =>
                                                    Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic._proof_1.{u_1,
                                                        u_2}
                                                      W hW n B hBW a)
                                                  z hz) :
                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B) →
                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B))
                                            q))
                                      (And
                                        (∀
                                          (z :
                                            ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2} B))
                                          (hz :
                                            Membership.mem.{u_1, u_1}
                                              (Metric.closedBall.{u_1}
                                                (0 :
                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                        u_2}
                                                      B))
                                                (↑a : Real))
                                              z)
                                          (v : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                                          LE.le.{0}
                                            (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                                              ((LinearEquiv.symm.{0, 0, u_2, u_2} (e z hz) :
                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B) →
                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2}
                                                        B))
                                                v))
                                            (HMul.hMul.{0, 0, 0} Cschur
                                              (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                                                v)))
                                        (And (LE.le.{0} Cschur (HMul.hMul.{0, 0, 0} (2 : Real) Cfull))
                                          (∀
                                            (z :
                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, u_2}
                                                  B))
                                            (hz :
                                              Membership.mem.{u_1, u_1}
                                                (Metric.closedBall.{u_1}
                                                  (0 :
                                                    ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                          u_2}
                                                        B))
                                                  (↑a : Real))
                                                z)
                                            (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, u_2} B)),
                                            LE.le.{0}
                                              (HMul.hMul.{0, 0, 0}
                                                (HDiv.hDiv.{0, 0, 0}
                                                  (HPow.hPow.{0, 0, 0}
                                                    (Erdos390.Full.PaperWeightedInverseExport.rawDLowerWeight.{u_2}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2}
                                                        B)
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B))
                                                    (2 : Nat))
                                                  (HMul.hMul.{0, 0, 0}
                                                    (Erdos390.Full.MovingLowGaugeTransfer.sharpWeightTotal.{u_2}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2}
                                                        B)
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B))
                                                    Cschur))
                                                (HPow.hPow.{0, 0, 0}
                                                  (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{u_2}
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, u_2} B)
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, u_2} B)
                                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{u_2}
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, u_2} B)
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, u_2} B))
                                                    q)
                                                  (2 : Nat)))
                                              (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, u_2} B
                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                          u_2}
                                                        B :
                                                      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                              u_2}
                                                            B) →
                                                        Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                    z))
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidualScore.{u_1,
                                                    u_2}
                                                  B
                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                          u_2}
                                                        B :
                                                      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                              u_2}
                                                            B) →
                                                        Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                    z)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                      u_2}
                                                    B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                      u_2}
                                                    B I a hU hlowerOne hupperU hlo hhi T hbaseline
                                                    (Decidable.byContradiction
                                                      fun
                                                        (a :
                                                          Not
                                                            (LT.lt.{0} (1 : Nat)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B)))) =>
                                                      Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic._proof_1.{u_1,
                                                          u_2}
                                                        W hW n B hBW a)
                                                    z hz)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.bandRegressionScore.{u_1,
                                                      u_2}
                                                    B q))
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidualScore.{u_1,
                                                    u_2}
                                                  B
                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1,
                                                          u_2}
                                                        B :
                                                      ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1,
                                                              u_2}
                                                            B) →
                                                        Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
                                                    z)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                      u_2}
                                                    B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                      u_2}
                                                    B I a hU hlowerOne hupperU hlo hhi T hbaseline
                                                    (Decidable.byContradiction
                                                      fun
                                                        (a :
                                                          Not
                                                            (LT.lt.{0} (1 : Nat)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1,
                                                                    u_2}
                                                                  B)))) =>
                                                      Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic._proof_1.{u_1,
                                                          u_2}
                                                        W hW n B hBW a)
                                                    z hz)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.bandRegressionScore.{u_1,
                                                      u_2}
                                                    B q))))))

noncomputable def Erdos390.AnalyticCompactGoal003 : Prop :=
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : @Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3)
  [inst_4 : Nonempty.{u_1 + 1} Head] (P : Head → Erdos390.Full.HeadPattern.Pattern)
  (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cmax : Real) {Cprom Cbank : Nat}
  (G :
    Erdos390.Full.PaperGuardCensus.Ledger
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))
      Cprom Cbank)
  (hsep :
    @LT.lt.{0} Nat instLTNat
      (Erdos390.Full.ArithmeticModel.physicalBound (I.upper Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)))
      (Erdos390.Full.ArithmeticModel.physicalBound (I.lower Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))))
  (hremaining :
    ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
      @Finset.Nonempty.{0} Nat
        (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))
            c)
          (@Erdos390.Full.PaperGuardCensus.Ledger.guards
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))
            Cprom Cbank G))),
  @Eq.{u_1 + 1} (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head inst)
      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)
      (@Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Head inst P I
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B))
        Cprom Cbank G hsep hremaining) →
    ∀ (xi : @Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)
      (hC_le : ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), @LE.le.{0} Real Real.instLE (I.upper sigma) Cmax),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)) →
        ∀ {K d : Real},
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) d →
              (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                  @LE.le.{0} Real Real.instLE
                    (@Erdos390.Full.PaperGuardCensus.valuationEnvelope.{u_1} Head inst I
                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                          inst_3 B))
                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                          inst_3 B))
                      c)
                    K) →
                (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                    @LT.lt.{0} Real Real.instLT
                      (@Erdos390.Full.FiniteProbability.guardMass.{0}
                        (@Subtype.{1} Nat fun (x : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c)
                            x)
                        (@Finset.Subtype.fintype.{0} Nat
                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            c))
                        (@Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                          (@Subtype.{1} Nat fun (x : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                              (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c)
                              x)
                          (@Finset.Subtype.fintype.{0} Nat
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c))
                          (@Erdos390.Full.FiniteProbability.uniformOnFinset.{0} Nat
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c)
                            (@Finset.Nonempty.mono.{0} Nat
                              (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  c)
                                (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  Cprom Cbank G))
                              (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c)
                              (@Finset.sdiff_subset.{0} Nat instDecidableEqNat
                                (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  c)
                                (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  Cprom Cbank G))
                              (hremaining c)))
                          fun
                            (m :
                              @Subtype.{1} Nat fun (x : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                  (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    c)
                                  x) =>
                          Erdos390.Full.ValuationScoreDomination.valuationScore
                            (Erdos390.Full.ArithmeticModel.primeBand
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B)))
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.effectiveNatCoefficient.{u_1, u_2} Head Band inst
                              inst_1 inst_2 inst_3 B xi)
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3
                              B)
                            (@Subtype.val.{1} Nat
                              (fun (x : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                  (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    c)
                                  x)
                              m))
                        (@Erdos390.Full.GuardedUniformCell.guardSubtype.{0} Nat instDecidableEqNat
                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            c)
                          (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            Cprom Cbank G)))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                  (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                      @LE.le.{0} Real Real.instLE
                        (@Erdos390.Full.FiniteProbability.guardPerturbation.{0}
                          (@Subtype.{1} Nat fun (x : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                              (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c)
                              x)
                          (@Finset.Subtype.fintype.{0} Nat
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c))
                          (@Erdos390.Full.FiniteProbability.exponentialTilt.{0}
                            (@Subtype.{1} Nat fun (x : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  c)
                                x)
                            (@Finset.Subtype.fintype.{0} Nat
                              (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c))
                            (@Erdos390.Full.FiniteProbability.uniformOnFinset.{0} Nat
                              (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c)
                              (@Finset.Nonempty.mono.{0} Nat
                                (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                  (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    c)
                                  (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    Cprom Cbank G))
                                (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  c)
                                (@Finset.sdiff_subset.{0} Nat instDecidableEqNat
                                  (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    c)
                                  (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    Cprom Cbank G))
                                (hremaining c)))
                            fun
                              (m :
                                @Subtype.{1} Nat fun (x : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_2 inst_3 B))
                                      c)
                                    x) =>
                            Erdos390.Full.ValuationScoreDomination.valuationScore
                              (Erdos390.Full.ArithmeticModel.primeBand
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B)))
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.effectiveNatCoefficient.{u_1, u_2} Head Band
                                inst inst_1 inst_2 inst_3 B xi)
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3
                                B)
                              (@Subtype.val.{1} Nat
                                (fun (x : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_2 inst_3 B))
                                      c)
                                    x)
                                m))
                          (@Erdos390.Full.GuardedUniformCell.guardSubtype.{0} Nat instDecidableEqNat
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c)
                            (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              Cprom Cbank G)))
                        d) →
                    ∀
                      (p :
                        Erdos390.Full.ArithmeticBandGeometry.BandPrime
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B))
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B))),
                      @LE.le.{0} Real Real.instLE
                        (@Finset.sum.{0, 0}
                          (Erdos390.Full.ArithmeticBandGeometry.BandPrime
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B)))
                          Real Real.instAddCommMonoid
                          (@Finset.univ.{0}
                            (Erdos390.Full.ArithmeticBandGeometry.BandPrime
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B)))
                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.instFintypeBandPrime
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))))
                          fun
                            (q :
                              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))) =>
                          @abs.{0} Real Real.lattice Real.instAddGroup
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleEndpoint.{u_1, u_2} Head Band inst
                                    inst_1 inst_2 inst_3 B)
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.canonicalGuardedMediumReferenceLaw.{u_1,
                                        u_2}
                                    Head Band inst inst_1 inst_2 inst_3 B inst_4 xi)
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B)))
                                        p)
                                    p)
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B)))
                                        p)
                                    q))
                                (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleEndpoint.{u_1, u_2} Head Band inst
                                    inst_1 inst_2 inst_3 B)
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.canonicalGuardedMediumReferenceLaw.{u_1,
                                        u_2}
                                    Head Band inst inst_1 inst_2 inst_3 B inst_4 xi)
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B)))
                                        p)
                                    p)
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B)))
                                        p)
                                    q)))
                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                                  (@Sigma.{u_1, 0} (Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                                    fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                    @Subtype.{1} Nat fun (x : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          c)
                                        x)
                                  (@Sigma.instFintype.{u_1, 0} (Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                                    (fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                      @Subtype.{1} Nat fun (x : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            c)
                                          x)
                                    (fun (i : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                      @Finset.Subtype.fintype.{0} Nat
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          i))
                                    (@instFintypeProd.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign inst
                                      Erdos390.Full.PaperBridgeFit.instFintypePhysicalSign))
                                  (Erdos390.Full.ArithmeticModel.physicalBound Cmax
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B)))
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.canonicalRawMediumReferenceLaw.{u_1, u_2}
                                    Head Band inst inst_1 inst_2 inst_3 B inst_4 P I Cmax xi hC_le
                                    fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                    @Finset.Nonempty.mono.{0} Nat
                                      (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          c)
                                        (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          Cprom Cbank G))
                                      (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        c)
                                      (@Finset.sdiff_subset.{0} Nat instDecidableEqNat
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          c)
                                        (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          Cprom Cbank G))
                                      (hremaining c))
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B)))
                                        p)
                                    p)
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B)))
                                        p)
                                    q))
                                (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                                  (@Sigma.{u_1, 0} (Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                                    fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                    @Subtype.{1} Nat fun (x : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          c)
                                        x)
                                  (@Sigma.instFintype.{u_1, 0} (Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                                    (fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                      @Subtype.{1} Nat fun (x : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))
                                            c)
                                          x)
                                    (fun (i : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                      @Finset.Subtype.fintype.{0} Nat
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          i))
                                    (@instFintypeProd.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign inst
                                      Erdos390.Full.PaperBridgeFit.instFintypePhysicalSign))
                                  (Erdos390.Full.ArithmeticModel.physicalBound Cmax
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B)))
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.canonicalRawMediumReferenceLaw.{u_1, u_2}
                                    Head Band inst inst_1 inst_2 inst_3 B inst_4 P I Cmax xi hC_le
                                    fun (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) =>
                                    @Finset.Nonempty.mono.{0} Nat
                                      (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          c)
                                        (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          Cprom Cbank G))
                                      (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        c)
                                      (@Finset.sdiff_subset.{0} Nat instDecidableEqNat
                                        (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          c)
                                        (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          Cprom Cbank G))
                                      (hremaining c))
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B)))
                                        p)
                                    p)
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B)))
                                        p)
                                    q)))))
                        (Erdos390.Full.PaperGuardCensus.guardPowerCorrectionRowError K d)

noncomputable def Erdos390.AnalyticCompactGoal004 : Prop :=
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
                (Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionMixtureBudget epsilon G n W (↑p : Nat))


