-- Prove2me | Definitions.Def_erdos390_remaining_analytic_propositions_003
-- name    : erdos390_remaining_analytic_propositions_003
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T16:41:14.81441+00:00
-- url     : https://prove2.me/theorems/85de43e5-7aaf-4456-b435-019c29c61a14
-- title:
--   Analytic construction propositions, part 3
-- statement:
--   Named propositions for the remaining analytic and finite construction estimates in the Erdős 390 central-anchor proof. Each name expands to the complete quantified statement, including every hypothesis and universe parameter. These definitions introduce no assertion of the propositions; their proofs are submitted separately. This part includes the following source declarations: exists_paperFineMesh_cutoff_eventually_canonical_lemma86_relativePrimePower, exists_paperFineMesh_cutoff_eventually_canonical_lemma86_variance_of_base, exists_structural_cutoff_eventually_canonical_actualFullQuotient.
-- source:
--   https://github.com/ShouqiaoW/erdos/tree/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean

import Definitions.Def_erdos390_analytic_foundations_001
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_analytic_nonstep_certificate
import Definitions.Def_erdos390_dickman_step_function
import Definitions.Def_erdos390_source_bank_interface
import Mathlib
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_MediumPNT
universe u_1
set_option maxRecDepth 10000
set_option maxHeartbeats 0


noncomputable def Erdos390.RemainingAnalyticGoal003_001 : Prop :=
∀ (cMesh : Real),
  LT.lt.{0} (0 : Real) cMesh →
    ∃ (meshTol : Real),
      And (LT.lt.{0} (0 : Real) meshTol)
        (∃ (Csharp : Real),
          And (LT.lt.{0} (0 : Real) Csharp)
            (∃ (Cordinary : Real),
              And (LT.lt.{0} (0 : Real) Cordinary)
                (∃ (Crow : Real),
                  And (LE.le.{0} (0 : Real) Crow)
                    (∃ (Creg : Real),
                      And (LE.le.{0} (0 : Real) Creg)
                        (And (Eq.{1} Creg (HMul.hMul.{0, 0, 0} Csharp (HMul.hMul.{0, 0, 0} (2 : Real) Crow)))
                          (∃ (Crel : Real),
                            And (LT.lt.{0} (0 : Real) Crel)
                              (∃ (W₀ : Nat),
                                ∀ (W : Nat),
                                  LE.le.{0} W₀ W →
                                    ∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) (hdelta : LT.lt.{0} (0 : Real) delta),
                                      Erdos390.Full.PaperPermittedRegularMesh.IsPermitted (cMesh := cMesh) M →
                                        LE.le.{0} (HAdd.hAdd.{0, 0, 0} delta eta) meshTol →
                                          ∀ (Head : Type u_1) [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head] [inst_2 : Nonempty.{u_1 + 1} Head]
                                            (Phead : Head → Erdos390.Full.HeadPattern.Pattern),
                                            (∀ (h : Head) (p : Nat), Iff (Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (Phead h)) p) (And (Nat.Prime p) (LE.le.{0} p W))) →
                                              ∀ (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (U : Real) (hU : LE.le.{0} (1 : Real) U)
                                                (hlowerOne :
                                                  ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma))
                                                (hupperU : ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) U)
                                                (Cprom Cbank : Nat) (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (a : NNReal) (marginFloor : Real),
                                                LT.lt.{0} (0 : Real) marginFloor →
                                                  ∃ (epsilonRel : Nat → Real),
                                                    And (∀ᶠ (n : Nat) in Filter.atTop.{0}, LE.le.{0} (0 : Real) (epsilonRel n))
                                                      (And (Filter.Tendsto.{0, 0} epsilonRel Filter.atTop.{0} (nhds.{0} (0 : Real)))
                                                        (And
                                                          (Filter.Tendsto.{0, 0} (fun (n : Nat) => HMul.hMul.{0, 0, 0} (epsilonRel n) (Real.log (Erdos390.Full.Scale.L n))) Filter.atTop.{0}
                                                            (nhds.{0} (0 : Real)))
                                                          (∀ᶠ (n : Nat) in Filter.atTop.{0},
                                                            ∀
                                                              (B :
                                                                Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, 0} Head
                                                                  (Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat)))),
                                                              Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) n →
                                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) W →
                                                                  ∀
                                                                    (hBWlarge :
                                                                      LT.lt.{0} (1 : Nat)
                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                    (hsep :
                                                                      LT.lt.{0}
                                                                        (Erdos390.Full.ArithmeticModel.physicalBound
                                                                          (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                        (Erdos390.Full.ArithmeticModel.physicalBound
                                                                          (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))))
                                                                    (hremaining :
                                                                      ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                                                                        Finset.Nonempty.{0}
                                                                          (SDiff.sdiff.{0}
                                                                            (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Phead I
                                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                              c)
                                                                            (Erdos390.Full.PaperGuardCensus.Ledger.guards (n :=
                                                                              Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                              (ledger
                                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))))))
                                                                    (hcanonical :
                                                                      Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)
                                                                        (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                          (ledger
                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                          hsep hremaining)),
                                                                    (∃ (hWne :
                                                                        Ne.{1}
                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                          (0 : Nat))
                                                                        (S :
                                                                        Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M
                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))),
                                                                        Eq.{1} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)
                                                                          (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, 0} B) hWne S)) →
                                                                      Eq.{1} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B) (HAdd.hAdd.{0, 0, 0} delta eta) →
                                                                        ∀ (T : Erdos390.Full.PaperGuardCensus.BarycentricTarget.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)),
                                                                          LE.le.{0} marginFloor (Erdos390.Full.PaperGuardCensus.BarycentricTarget.cellMassMargin.{u_1} T) →
                                                                            ∀
                                                                              (hbaseline :
                                                                                Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1, 0} B)
                                                                                  (Erdos390.Full.PaperGuardCensus.BarycentricTarget.baseline.{u_1} T)),
                                                                              And
                                                                                (∀
                                                                                  (p :
                                                                                    Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))),
                                                                                  LE.le.{0}
                                                                                    (abs.{0}
                                                                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.deviation.{0}
                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B) p))
                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B))
                                                                                (And
                                                                                  (LE.le.{0}
                                                                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.totalL1.{0}
                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                                                    (HMul.hMul.{0, 0, 0} (7 : Real) (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B)))
                                                                                  (And
                                                                                    (LE.le.{0} (HPow.hPow.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B) (2 : Nat))
                                                                                      (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (456 : Real) (HPow.hPow.{0, 0, 0} cMesh (2 : Nat)))
                                                                                        (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{0}
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))))
                                                                                    (And
                                                                                      (LE.le.{0}
                                                                                        (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{0}
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                                                        (HMul.hMul.{0, 0, 0} (4 : Real)
                                                                                          (HPow.hPow.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B) (2 : Nat))))
                                                                                      (And
                                                                                        (LE.le.{0}
                                                                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{0}
                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.centerEnergy.{0}
                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)))
                                                                                        (∃ (e :
                                                                                          (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                            Membership.mem.{u_1, u_1}
                                                                                                (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B))
                                                                                                  (↑a : Real))
                                                                                                z →
                                                                                              LinearEquiv.{0, 0, 0, 0} (RingHom.id.{0} Real)
                                                                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)
                                                                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)),
                                                                                          And
                                                                                            (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B))
                                                                                              (hz :
                                                                                                Membership.mem.{u_1, u_1}
                                                                                                  (Metric.closedBall.{u_1}
                                                                                                    (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) (↑a : Real))
                                                                                                  z)
                                                                                              (q : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)),
                                                                                              Eq.{1} (α := ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                                                ((e z hz :
                                                                                                      (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)) →
                                                                                                        ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                                                    q :
                                                                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                                                ((Erdos390.Full.PaperBridgeFit.BridgeData.actualBandSchurLinearMap.{u_1, 0} B
                                                                                                        ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                            (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                                              Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                          z)
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, 0} B I U
                                                                                                          (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1, 0} B
                                                                                                          I a hU hlowerOne hupperU
                                                                                                          (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                            Eq.mpr.{0}
                                                                                                              (id.{0}
                                                                                                                (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                  (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                    Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                                                      (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                        (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                  hcanonical))
                                                                                                              (Eq.refl.{1}
                                                                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                                                  (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                    Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                    (ledger
                                                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                    hsep hremaining)
                                                                                                                  sigma)))
                                                                                                          (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                            Eq.mpr.{0}
                                                                                                              (id.{0}
                                                                                                                (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                  (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                    Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                                                      (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                        (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                  hcanonical))
                                                                                                              (Eq.refl.{1}
                                                                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                                                  (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                    Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                    (ledger
                                                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                    hsep hremaining)
                                                                                                                  sigma)))
                                                                                                          T hbaseline hBWlarge z hz) :
                                                                                                      (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)) →
                                                                                                        ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                                                    q :
                                                                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)))
                                                                                            (And
                                                                                              (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B))
                                                                                                (hz :
                                                                                                  Membership.mem.{u_1, u_1}
                                                                                                    (Metric.closedBall.{u_1}
                                                                                                      (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) (↑a : Real))
                                                                                                    z)
                                                                                                (v : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)),
                                                                                                LE.le.{0}
                                                                                                  (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{0}
                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, 0} B)
                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, 0} B)
                                                                                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{0}
                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)
                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, 0} B))
                                                                                                    ((LinearEquiv.symm.{0, 0, 0, 0} (e z hz) :
                                                                                                        (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)) →
                                                                                                          ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                                                      v))
                                                                                                  (HMul.hMul.{0, 0, 0} Csharp
                                                                                                    (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{0}
                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, 0} B)
                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, 0} B)
                                                                                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{0}
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, 0} B))
                                                                                                      v)))
                                                                                              (And
                                                                                                (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B))
                                                                                                  (hz :
                                                                                                    Membership.mem.{u_1, u_1}
                                                                                                      (Metric.closedBall.{u_1}
                                                                                                        (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) (↑a : Real))
                                                                                                      z)
                                                                                                  (v : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)),
                                                                                                  LE.le.{0}
                                                                                                    (Norm.norm.{0} (E := ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                                                      ((LinearEquiv.symm.{0, 0, 0, 0} (e z hz) :
                                                                                                            (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)) →
                                                                                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                                                          v :
                                                                                                        ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)))
                                                                                                    (HMul.hMul.{0, 0, 0} Cordinary (Norm.norm.{0} v)))
                                                                                                (∀ (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B))
                                                                                                  (hz :
                                                                                                    Membership.mem.{u_1, u_1}
                                                                                                      (Metric.closedBall.{u_1}
                                                                                                        (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) (↑a : Real))
                                                                                                      z),
                                                                                                  And
                                                                                                    (∀ (j : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))),
                                                                                                      LE.le.{0}
                                                                                                        (abs.{0}
                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.normalizedBandCovarianceRow.{u_1, 0} B
                                                                                                            ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                                (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                                                  Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                              z)
                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidualScore.{u_1, 0} B
                                                                                                              ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                                  (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                                                    Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                                z)
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, 0} B I
                                                                                                                U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                                                                                  0}
                                                                                                                B I a hU hlowerOne hupperU
                                                                                                                (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                  Eq.mpr.{0}
                                                                                                                    (id.{0}
                                                                                                                      (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                        (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                                                            (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                              (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                        hcanonical))
                                                                                                                    (Eq.refl.{1}
                                                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                                                        (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                          (ledger
                                                                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                          hsep hremaining)
                                                                                                                        sigma)))
                                                                                                                (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                  Eq.mpr.{0}
                                                                                                                    (id.{0}
                                                                                                                      (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                        (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                                                            (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                              (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                        hcanonical))
                                                                                                                    (Eq.refl.{1}
                                                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                                                        (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                          (ledger
                                                                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                          hsep hremaining)
                                                                                                                        sigma)))
                                                                                                                T hbaseline hBWlarge z hz)
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.slowScore.{u_1, 0} B))
                                                                                                            j))
                                                                                                        (HMul.hMul.{0, 0, 0}
                                                                                                          (HMul.hMul.{0, 0, 0} Crow (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B))
                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, 0} B j)))
                                                                                                    (And
                                                                                                      (Eq.{1}
                                                                                                        ((Erdos390.Full.PaperBridgeFit.BridgeData.actualBandSchurLinearMap.{u_1, 0} B
                                                                                                              ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                                  (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                                                    Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                                z)
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, 0} B I
                                                                                                                U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                                                                                  0}
                                                                                                                B I a hU hlowerOne hupperU
                                                                                                                (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                  Eq.mpr.{0}
                                                                                                                    (id.{0}
                                                                                                                      (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                        (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                                                            (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                              (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                        hcanonical))
                                                                                                                    (Eq.refl.{1}
                                                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                                                        (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                          (ledger
                                                                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                          hsep hremaining)
                                                                                                                        sigma)))
                                                                                                                (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                  Eq.mpr.{0}
                                                                                                                    (id.{0}
                                                                                                                      (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                        (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                                                            (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                              (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                        hcanonical))
                                                                                                                    (Eq.refl.{1}
                                                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                                                        (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                          (ledger
                                                                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                          hsep hremaining)
                                                                                                                        sigma)))
                                                                                                                T hbaseline hBWlarge z hz) :
                                                                                                            (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)) →
                                                                                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B))
                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1, 0} B
                                                                                                            ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                                (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                                                  Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                              z)
                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, 0} B I U
                                                                                                              (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                                                                                0}
                                                                                                              B I a hU hlowerOne hupperU
                                                                                                              (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                Eq.mpr.{0}
                                                                                                                  (id.{0}
                                                                                                                    (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                      (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                        Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                                                          (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                            (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                      hcanonical))
                                                                                                                  (Eq.refl.{1}
                                                                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                                                      (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                        (ledger
                                                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                        hsep hremaining)
                                                                                                                      sigma)))
                                                                                                              (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                Eq.mpr.{0}
                                                                                                                  (id.{0}
                                                                                                                    (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                      (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                        Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                                                          (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                            (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                      hcanonical))
                                                                                                                  (Eq.refl.{1}
                                                                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                                                      (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                        (ledger
                                                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                        hsep hremaining)
                                                                                                                      sigma)))
                                                                                                              T hbaseline hBWlarge z hz)
                                                                                                            (e z hz)))
                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegressionTarget.{u_1, 0} B
                                                                                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                              (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                                                Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                            z)
                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, 0} B I U
                                                                                                            (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1, 0}
                                                                                                            B I a hU hlowerOne hupperU
                                                                                                            (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                              Eq.mpr.{0}
                                                                                                                (id.{0}
                                                                                                                  (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                    (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                      Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                                                        (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                          (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                    hcanonical))
                                                                                                                (Eq.refl.{1}
                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                      (ledger
                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                      hsep hremaining)
                                                                                                                    sigma)))
                                                                                                            (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                              Eq.mpr.{0}
                                                                                                                (id.{0}
                                                                                                                  (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                    (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                      Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                                                        (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                          (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                    hcanonical))
                                                                                                                (Eq.refl.{1}
                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                      (ledger
                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                      hsep hremaining)
                                                                                                                    sigma)))
                                                                                                            T hbaseline hBWlarge z hz)))
                                                                                                      (And
                                                                                                        (LE.le.{0}
                                                                                                          (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{0}
                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, 0} B)
                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, 0} B)
                                                                                                            (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{0}
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, 0} B))
                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1, 0} B
                                                                                                              ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                                  (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                                                    Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                                z)
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, 0} B I
                                                                                                                U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                                                                                  0}
                                                                                                                B I a hU hlowerOne hupperU
                                                                                                                (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                  Eq.mpr.{0}
                                                                                                                    (id.{0}
                                                                                                                      (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                        (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                                                            (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                              (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                        hcanonical))
                                                                                                                    (Eq.refl.{1}
                                                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                                                        (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                          (ledger
                                                                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                          hsep hremaining)
                                                                                                                        sigma)))
                                                                                                                (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                  Eq.mpr.{0}
                                                                                                                    (id.{0}
                                                                                                                      (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                        (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                                                            (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                              (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                        hcanonical))
                                                                                                                    (Eq.refl.{1}
                                                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                                                        (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                          (ledger
                                                                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                          hsep hremaining)
                                                                                                                        sigma)))
                                                                                                                T hbaseline hBWlarge z hz)
                                                                                                              (e z hz)))
                                                                                                          (HMul.hMul.{0, 0, 0} Creg (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B)))
                                                                                                        (And
                                                                                                          (∀
                                                                                                            (p :
                                                                                                              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))),
                                                                                                            LE.le.{0}
                                                                                                              (abs.{0}
                                                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.actualCompensatedCoefficient.{u_1, 0} B
                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1, 0} B
                                                                                                                    ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                                        (a :
                                                                                                                            ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                                                          Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                                      z)
                                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                                                                                        0}
                                                                                                                      B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                                                                                        0}
                                                                                                                      B I a hU hlowerOne hupperU
                                                                                                                      (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                        Eq.mpr.{0}
                                                                                                                          (id.{0}
                                                                                                                            (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                              (fun
                                                                                                                                  (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                                Eq.{1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                                                                  (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                                    (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                              hcanonical))
                                                                                                                          (Eq.refl.{1}
                                                                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                                                              (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                                Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                                (ledger
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                                hsep hremaining)
                                                                                                                              sigma)))
                                                                                                                      (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                        Eq.mpr.{0}
                                                                                                                          (id.{0}
                                                                                                                            (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                              (fun
                                                                                                                                  (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                                Eq.{1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                                                                  (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                                    (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                              hcanonical))
                                                                                                                          (Eq.refl.{1}
                                                                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                                                              (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                                Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                                (ledger
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                                hsep hremaining)
                                                                                                                              sigma)))
                                                                                                                      T hbaseline hBWlarge z hz)
                                                                                                                    (e z hz))
                                                                                                                  p))
                                                                                                              (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (1 : Real) Creg)
                                                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B)))
                                                                                                          (And
                                                                                                            (LE.le.{0}
                                                                                                              (Erdos390.Full.ArithmeticBandGeometry.Partition.compensatedL1.{0}
                                                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)
                                                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1, 0} B
                                                                                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                                      (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                                                        Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                                    z)
                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, 0}
                                                                                                                    B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                                                                                      0}
                                                                                                                    B I a hU hlowerOne hupperU
                                                                                                                    (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                      Eq.mpr.{0}
                                                                                                                        (id.{0}
                                                                                                                          (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                            (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                              Eq.{1}
                                                                                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                                                                (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                                  (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                            hcanonical))
                                                                                                                        (Eq.refl.{1}
                                                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                                                            (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                              Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                              (ledger
                                                                                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                              hsep hremaining)
                                                                                                                            sigma)))
                                                                                                                    (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                      Eq.mpr.{0}
                                                                                                                        (id.{0}
                                                                                                                          (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                            (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                              Eq.{1}
                                                                                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                                                                (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                                  (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                            hcanonical))
                                                                                                                        (Eq.refl.{1}
                                                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                                                            (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                              Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                              (ledger
                                                                                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                              hsep hremaining)
                                                                                                                            sigma)))
                                                                                                                    T hbaseline hBWlarge z hz)
                                                                                                                  (e z hz)))
                                                                                                              (HMul.hMul.{0, 0, 0}
                                                                                                                (HAdd.hAdd.{0, 0, 0} (7 : Real)
                                                                                                                  (HMul.hMul.{0, 0, 0} Creg (HMul.hMul.{0, 0, 0} (2 : Real) (Real.log (4 : Real)))))
                                                                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B)))
                                                                                                            (And
                                                                                                              (LE.le.{0}
                                                                                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.compensatedL2Sq.{0}
                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)
                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1, 0} B
                                                                                                                    ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                                        (a :
                                                                                                                            ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                                                          Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                                      z)
                                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                                                                                        0}
                                                                                                                      B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                                                                                        0}
                                                                                                                      B I a hU hlowerOne hupperU
                                                                                                                      (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                        Eq.mpr.{0}
                                                                                                                          (id.{0}
                                                                                                                            (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                              (fun
                                                                                                                                  (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                                Eq.{1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                                                                  (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                                    (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                              hcanonical))
                                                                                                                          (Eq.refl.{1}
                                                                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                                                              (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                                Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                                (ledger
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                                hsep hremaining)
                                                                                                                              sigma)))
                                                                                                                      (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                        Eq.mpr.{0}
                                                                                                                          (id.{0}
                                                                                                                            (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                              (fun
                                                                                                                                  (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                                                                Eq.{1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                                                                  (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                                    (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                                                              hcanonical))
                                                                                                                          (Eq.refl.{1}
                                                                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                                                              (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                                                                Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                                (ledger
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                                                                hsep hremaining)
                                                                                                                              sigma)))
                                                                                                                      T hbaseline hBWlarge z hz)
                                                                                                                    (e z hz)))
                                                                                                                (HMul.hMul.{0, 0, 0}
                                                                                                                  (HMul.hMul.{0, 0, 0} (2 : Real)
                                                                                                                    (HAdd.hAdd.{0, 0, 0} (4 : Real)
                                                                                                                      (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} Creg (2 : Nat))
                                                                                                                        (HMul.hMul.{0, 0, 0} (2 : Real) (Real.log (4 : Real))))))
                                                                                                                  (HPow.hPow.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B)
                                                                                                                    (2 : Nat))))
                                                                                                              (LE.le.{0}
                                                                                                                (abs.{0}
                                                                                                                  (HSub.hSub.{0, 0, 0}
                                                                                                                    (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, 0} B
                                                                                                                        ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                                            (a :
                                                                                                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0}
                                                                                                                                    B)) →
                                                                                                                              Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                                          z))
                                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.postBandPrimeScore.{u_1, 0} B
                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1, 0} B
                                                                                                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                                              (a :
                                                                                                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0}
                                                                                                                                      B)) →
                                                                                                                                Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                                            z)
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                                                                                              0}
                                                                                                                            B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                                                                                              0}
                                                                                                                            B I a hU hlowerOne hupperU
                                                                                                                            (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                              Eq.mpr.{0}
                                                                                                                                (id.{0}
                                                                                                                                  (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                                    (fun
                                                                                                                                        (_a :
                                                                                                                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1}
                                                                                                                                            Head) =>
                                                                                                                                      Eq.{1}
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a
                                                                                                                                          sigma)
                                                                                                                                        (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                                          (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I
                                                                                                                                            sigma)
                                                                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                            _a)))
                                                                                                                                    hcanonical))
                                                                                                                                (Eq.refl.{1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I
                                                                                                                                      (W :=
                                                                                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                                      (ledger
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0}
                                                                                                                                            B)))
                                                                                                                                      hsep hremaining)
                                                                                                                                    sigma)))
                                                                                                                            (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                              Eq.mpr.{0}
                                                                                                                                (id.{0}
                                                                                                                                  (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                                    (fun
                                                                                                                                        (_a :
                                                                                                                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1}
                                                                                                                                            Head) =>
                                                                                                                                      Eq.{1}
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a
                                                                                                                                          sigma)
                                                                                                                                        (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                                          (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I
                                                                                                                                            sigma)
                                                                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                            _a)))
                                                                                                                                    hcanonical))
                                                                                                                                (Eq.refl.{1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I
                                                                                                                                      (W :=
                                                                                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                                      (ledger
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0}
                                                                                                                                            B)))
                                                                                                                                      hsep hremaining)
                                                                                                                                    sigma)))
                                                                                                                            T hbaseline hBWlarge z hz)
                                                                                                                          (e z hz)))
                                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.postBandPrimeScore.{u_1, 0} B
                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1, 0} B
                                                                                                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                                              (a :
                                                                                                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0}
                                                                                                                                      B)) →
                                                                                                                                Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                                            z)
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                                                                                              0}
                                                                                                                            B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                                                                                              0}
                                                                                                                            B I a hU hlowerOne hupperU
                                                                                                                            (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                              Eq.mpr.{0}
                                                                                                                                (id.{0}
                                                                                                                                  (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                                    (fun
                                                                                                                                        (_a :
                                                                                                                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1}
                                                                                                                                            Head) =>
                                                                                                                                      Eq.{1}
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a
                                                                                                                                          sigma)
                                                                                                                                        (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                                          (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I
                                                                                                                                            sigma)
                                                                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                            _a)))
                                                                                                                                    hcanonical))
                                                                                                                                (Eq.refl.{1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I
                                                                                                                                      (W :=
                                                                                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                                      (ledger
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0}
                                                                                                                                            B)))
                                                                                                                                      hsep hremaining)
                                                                                                                                    sigma)))
                                                                                                                            (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                              Eq.mpr.{0}
                                                                                                                                (id.{0}
                                                                                                                                  (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                                    (fun
                                                                                                                                        (_a :
                                                                                                                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1}
                                                                                                                                            Head) =>
                                                                                                                                      Eq.{1}
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a
                                                                                                                                          sigma)
                                                                                                                                        (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                                          (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I
                                                                                                                                            sigma)
                                                                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                            _a)))
                                                                                                                                    hcanonical))
                                                                                                                                (Eq.refl.{1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I
                                                                                                                                      (W :=
                                                                                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                                      (ledger
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0}
                                                                                                                                            B)))
                                                                                                                                      hsep hremaining)
                                                                                                                                    sigma)))
                                                                                                                            T hbaseline hBWlarge z hz)
                                                                                                                          (e z hz))))
                                                                                                                    (Erdos390.Full.FiniteProbability.covariance.{u_1}
                                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, 0} B
                                                                                                                        ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                                            (a :
                                                                                                                                ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0}
                                                                                                                                    B)) →
                                                                                                                              Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                                          z))
                                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.postBandSquarefreeScore.{u_1, 0} B
                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1, 0} B
                                                                                                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                                              (a :
                                                                                                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0}
                                                                                                                                      B)) →
                                                                                                                                Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                                            z)
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                                                                                              0}
                                                                                                                            B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                                                                                              0}
                                                                                                                            B I a hU hlowerOne hupperU
                                                                                                                            (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                              Eq.mpr.{0}
                                                                                                                                (id.{0}
                                                                                                                                  (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                                    (fun
                                                                                                                                        (_a :
                                                                                                                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1}
                                                                                                                                            Head) =>
                                                                                                                                      Eq.{1}
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a
                                                                                                                                          sigma)
                                                                                                                                        (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                                          (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I
                                                                                                                                            sigma)
                                                                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                            _a)))
                                                                                                                                    hcanonical))
                                                                                                                                (Eq.refl.{1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I
                                                                                                                                      (W :=
                                                                                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                                      (ledger
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0}
                                                                                                                                            B)))
                                                                                                                                      hsep hremaining)
                                                                                                                                    sigma)))
                                                                                                                            (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                              Eq.mpr.{0}
                                                                                                                                (id.{0}
                                                                                                                                  (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                                    (fun
                                                                                                                                        (_a :
                                                                                                                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1}
                                                                                                                                            Head) =>
                                                                                                                                      Eq.{1}
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a
                                                                                                                                          sigma)
                                                                                                                                        (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                                          (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I
                                                                                                                                            sigma)
                                                                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                            _a)))
                                                                                                                                    hcanonical))
                                                                                                                                (Eq.refl.{1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I
                                                                                                                                      (W :=
                                                                                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                                      (ledger
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0}
                                                                                                                                            B)))
                                                                                                                                      hsep hremaining)
                                                                                                                                    sigma)))
                                                                                                                            T hbaseline hBWlarge z hz)
                                                                                                                          (e z hz)))
                                                                                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.postBandSquarefreeScore.{u_1, 0} B
                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1, 0} B
                                                                                                                          ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                                                              (a :
                                                                                                                                  ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0}
                                                                                                                                      B)) →
                                                                                                                                Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                                                                            z)
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1,
                                                                                                                              0}
                                                                                                                            B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1,
                                                                                                                              0}
                                                                                                                            B I a hU hlowerOne hupperU
                                                                                                                            (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                              Eq.mpr.{0}
                                                                                                                                (id.{0}
                                                                                                                                  (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                                    (fun
                                                                                                                                        (_a :
                                                                                                                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1}
                                                                                                                                            Head) =>
                                                                                                                                      Eq.{1}
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a
                                                                                                                                          sigma)
                                                                                                                                        (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                                          (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I
                                                                                                                                            sigma)
                                                                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                            _a)))
                                                                                                                                    hcanonical))
                                                                                                                                (Eq.refl.{1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I
                                                                                                                                      (W :=
                                                                                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                                      (ledger
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0}
                                                                                                                                            B)))
                                                                                                                                      hsep hremaining)
                                                                                                                                    sigma)))
                                                                                                                            (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                                                              Eq.mpr.{0}
                                                                                                                                (id.{0}
                                                                                                                                  (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                                                                    (fun
                                                                                                                                        (_a :
                                                                                                                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1}
                                                                                                                                            Head) =>
                                                                                                                                      Eq.{1}
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a
                                                                                                                                          sigma)
                                                                                                                                        (Erdos390.Full.ArithmeticModel.physicalBound
                                                                                                                                          (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I
                                                                                                                                            sigma)
                                                                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                            _a)))
                                                                                                                                    hcanonical))
                                                                                                                                (Eq.refl.{1}
                                                                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I
                                                                                                                                      (W :=
                                                                                                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                                                                      (ledger
                                                                                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0}
                                                                                                                                            B)))
                                                                                                                                      hsep hremaining)
                                                                                                                                    sigma)))
                                                                                                                            T hbaseline hBWlarge z hz)
                                                                                                                          (e z hz))))))
                                                                                                                (HMul.hMul.{0, 0, 0}
                                                                                                                  (HAdd.hAdd.{0, 0, 0}
                                                                                                                    (HMul.hMul.{0, 0, 0} Crel
                                                                                                                      (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                                                                        (↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) :
                                                                                                                          Real)))
                                                                                                                    (epsilonRel
                                                                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))))
                                                                                                                  (HPow.hPow.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B)
                                                                                                                    (2 : Nat)))))))))))))))))))))))))))

noncomputable def Erdos390.RemainingAnalyticGoal003_002 : Prop :=
∀ (cMesh Creg : Real),
  LT.lt.{0} (0 : Real) cMesh →
    LE.le.{0} (0 : Real) Creg →
      ∃ (meshTol : Real),
        And (LT.lt.{0} (0 : Real) meshTol)
          (∃ (gammaSlow : Real),
            And (LT.lt.{0} (0 : Real) gammaSlow)
              (∃ (Cvar : Real),
                And (LT.lt.{0} (0 : Real) Cvar)
                  (∃ (W₀ : Nat),
                    ∀ (W : Nat),
                      LE.le.{0} W₀ W →
                        ∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) (hdelta : LT.lt.{0} (0 : Real) delta),
                          Erdos390.Full.PaperPermittedRegularMesh.IsPermitted (cMesh := cMesh) M →
                            LE.le.{0} (HAdd.hAdd.{0, 0, 0} delta eta) meshTol →
                              ∀ {Head : Type u_1} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head] [inst_2 : Nonempty.{u_1 + 1} Head]
                                (Phead : Head → Erdos390.Full.HeadPattern.Pattern),
                                (∀ (h : Head) (p : Nat), Iff (Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (Phead h)) p) (And (Nat.Prime p) (LE.le.{0} p W))) →
                                  ∀ (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (U : Real) (hU : LE.le.{0} (1 : Real) U)
                                    (hlowerOne : ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma))
                                    (hupperU : ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) U) (Cprom Cbank : Nat)
                                    (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (a : NNReal) (marginFloor : Real),
                                    LT.lt.{0} (0 : Real) marginFloor →
                                      ∀ᶠ (n : Nat) in Filter.atTop.{0},
                                        ∀ (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, 0} Head (Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat)))),
                                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) n →
                                            Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) W →
                                              ∀
                                                (hBWlarge :
                                                  LT.lt.{0} (1 : Nat) (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                (hsep :
                                                  LT.lt.{0}
                                                    (Erdos390.Full.ArithmeticModel.physicalBound
                                                      (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                    (Erdos390.Full.ArithmeticModel.physicalBound
                                                      (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))))
                                                (hremaining :
                                                  ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                                                    Finset.Nonempty.{0}
                                                      (SDiff.sdiff.{0}
                                                        (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Phead I
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) c)
                                                        (Erdos390.Full.PaperGuardCensus.Ledger.guards (n :=
                                                          Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                          (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))))))
                                                (hcanonical :
                                                  Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)
                                                    (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                      Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                      (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))) hsep
                                                      hremaining)),
                                                (∃ (hWne : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) (0 : Nat))
                                                    (S :
                                                    Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))),
                                                    Eq.{1} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)
                                                      (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, 0} B) hWne S)) →
                                                  Eq.{1} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B) (HAdd.hAdd.{0, 0, 0} delta eta) →
                                                    ∀ (T : Erdos390.Full.PaperGuardCensus.BarycentricTarget.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)),
                                                      LE.le.{0} marginFloor (Erdos390.Full.PaperGuardCensus.BarycentricTarget.cellMassMargin.{u_1} T) →
                                                        ∀
                                                          (hbaseline :
                                                            Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1, 0} B)
                                                              (Erdos390.Full.PaperGuardCensus.BarycentricTarget.baseline.{u_1} T))
                                                          (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B))
                                                          (hz :
                                                            Membership.mem.{u_1, u_1}
                                                              (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) (↑a : Real)) z)
                                                          (e :
                                                            LinearEquiv.{0, 0, 0, 0} (RingHom.id.{0} Real) ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)
                                                              ↥(Erdos390.Full.PaperBridgeFit.BridgeData.RawBandGauge.{u_1, 0} B)),
                                                          LE.le.{0}
                                                              (Erdos390.Full.PaperWeightedInverseExport.paperSharpNorm.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.harmonicMass.{u_1, 0} B)
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.bandCenter.{u_1, 0} B)
                                                                (Erdos390.Full.ArithmeticBandGeometry.Partition.center_ne_zero.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, 0} B))
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.actualBandRegression.{u_1, 0} B
                                                                  ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                      (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                        Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                    z)
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, 0} B I U
                                                                    (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1, 0} B I a hU hlowerOne hupperU
                                                                    (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                      Eq.mpr.{0}
                                                                        (id.{0}
                                                                          (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                            (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                              Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                            hcanonical))
                                                                        (Eq.refl.{1}
                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                            (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                              Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                              (ledger
                                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                              hsep hremaining)
                                                                            sigma)))
                                                                    (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                      Eq.mpr.{0}
                                                                        (id.{0}
                                                                          (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                            (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                              Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                            hcanonical))
                                                                        (Eq.refl.{1}
                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                            (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                              Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                              (ledger
                                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                              hsep hremaining)
                                                                            sigma)))
                                                                    T hbaseline hBWlarge z hz)
                                                                  e))
                                                              (HMul.hMul.{0, 0, 0} Creg (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B)) →
                                                            (∀
                                                                (p :
                                                                  Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))),
                                                                LE.le.{0}
                                                                  (abs.{0}
                                                                    (Erdos390.Full.ArithmeticBandGeometry.Partition.deviation.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B) p))
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B)) →
                                                              LE.le.{0} (Erdos390.Full.ArithmeticBandGeometry.Partition.totalL1.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                                  (HMul.hMul.{0, 0, 0} (7 : Real) (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B)) →
                                                                LE.le.{0} (HPow.hPow.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B) (2 : Nat))
                                                                    (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (456 : Real) (HPow.hPow.{0, 0, 0} cMesh (2 : Nat)))
                                                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))) →
                                                                  LE.le.{0} (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                                      (HMul.hMul.{0, 0, 0} (4 : Real) (HPow.hPow.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B) (2 : Nat))) →
                                                                    LE.le.{0}
                                                                        (Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                                        (Erdos390.Full.ArithmeticBandGeometry.Partition.centerEnergy.{0}
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)) →
                                                                      And
                                                                        (LE.le.{0}
                                                                          (HMul.hMul.{0, 0, 0} gammaSlow (HPow.hPow.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B) (2 : Nat)))
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.actualTwoStageCompensatedVariance.{u_1, 0} B
                                                                            ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                  Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                              z)
                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, 0} B I U
                                                                              (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1, 0} B I a hU hlowerOne hupperU
                                                                              (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                Eq.mpr.{0}
                                                                                  (id.{0}
                                                                                    (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                      (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                        Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                          (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                      hcanonical))
                                                                                  (Eq.refl.{1}
                                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                      (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                        (ledger
                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                        hsep hremaining)
                                                                                      sigma)))
                                                                              (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                Eq.mpr.{0}
                                                                                  (id.{0}
                                                                                    (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                      (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                        Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                          (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                      hcanonical))
                                                                                  (Eq.refl.{1}
                                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                      (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                        (ledger
                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                        hsep hremaining)
                                                                                      sigma)))
                                                                              T hbaseline hBWlarge z hz)
                                                                            e))
                                                                        (LE.le.{0}
                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.actualTwoStageCompensatedVariance.{u_1, 0} B
                                                                            ((Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                                                (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) →
                                                                                  Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                                              z)
                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, 0} B I U
                                                                              (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T)
                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1, 0} B I a hU hlowerOne hupperU
                                                                              (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                Eq.mpr.{0}
                                                                                  (id.{0}
                                                                                    (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                      (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                        Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                                          (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                      hcanonical))
                                                                                  (Eq.refl.{1}
                                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                                                      (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                        (ledger
                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                        hsep hremaining)
                                                                                      sigma)))
                                                                              (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                                                Eq.mpr.{0}
                                                                                  (id.{0}
                                                                                    (congrArg.{u_1 + 1, 1} (β := Prop)
                                                                                      (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                                                        Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                                          (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                                                      hcanonical))
                                                                                  (Eq.refl.{1}
                                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                                                      (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                                                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                                                        (ledger
                                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                                                                        hsep hremaining)
                                                                                      sigma)))
                                                                              T hbaseline hBWlarge z hz)
                                                                            e)
                                                                          (HMul.hMul.{0, 0, 0} Cvar (HPow.hPow.{0, 0, 0} (Erdos390.Full.PaperBridgeFit.BridgeData.w.{u_1, 0} B) (2 : Nat)))))))

noncomputable def Erdos390.RemainingAnalyticGoal003_003 : Prop :=
∃ (kappa : Real),
  And (LT.lt.{0} (0 : Real) kappa)
    (∃ (W₀ : Nat),
      ∀ (W : Nat),
        LE.le.{0} W₀ W →
          ∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) (hdelta : LT.lt.{0} (0 : Real) delta)
            (anchors : Finset.{0} (Fin (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M))),
            Finset.Nonempty.{0} anchors →
              (∀ (k : Fin (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M)), Membership.mem.{0, 0} anchors k → LT.lt.{0} (1 / 8 : Real) (Erdos390.Full.RegularRelativeMesh.Mesh.lower M k)) →
                (∀ (k : Fin (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M)),
                    Membership.mem.{0, 0} anchors k → LE.le.{0} (Erdos390.Full.RegularRelativeMesh.Mesh.upper M k) (HSub.hSub.{0, 0, 0} (1 : Real) (1 / 8 : Real))) →
                  LE.le.{0} (1 / 8 : Real) (HDiv.hDiv.{0, 0, 0} (∑ k ∈ anchors, Erdos390.Full.RegularRelativeMesh.Mesh.width M k) (2 : Real)) →
                    ∀ {Head : Type u_1} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head] [inst_2 : Nonempty.{u_1 + 1} Head] (Phead : Head → Erdos390.Full.HeadPattern.Pattern),
                      (∀ (h : Head) (p : Nat), Iff (Membership.mem.{0, 0} (Erdos390.Full.HeadPattern.Pattern.primes (Phead h)) p) (And (Nat.Prime p) (LE.le.{0} p W))) →
                        ∀ (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (U : Real) (hU : LE.le.{0} (1 : Real) U)
                          (hlowerOne : ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (1 : Real) (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma))
                          (hupperU : ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign), LE.le.{0} (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma) U) (Cprom Cbank : Nat)
                          (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (a : NNReal) (marginFloor : Real),
                          LT.lt.{0} (0 : Real) marginFloor →
                            ∀ᶠ (n : Nat) in Filter.atTop.{0},
                              ∀ (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, 0} Head (Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat)))),
                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) n →
                                  Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) W →
                                    ∀ (hBWlarge : LT.lt.{0} (1 : Nat) (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                      (hsep :
                                        LT.lt.{0}
                                          (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)))
                                          (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))))
                                      (hremaining :
                                        ∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                                          Finset.Nonempty.{0}
                                            (SDiff.sdiff.{0}
                                              (Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Phead I
                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) c)
                                              (Erdos390.Full.PaperGuardCensus.Ledger.guards (n :=
                                                Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))))))
                                      (hcanonical :
                                        Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)
                                          (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                            Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                            (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))) hsep hremaining)),
                                      (∃ (hWne : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)) (0 : Nat)) (S :
                                          Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))),
                                          Eq.{1} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)
                                            (Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta (Erdos390.Full.PaperBridgeFit.BridgeData.n_gt_one.{u_1, 0} B) hWne S)) →
                                        ∀ (T : Erdos390.Full.PaperGuardCensus.BarycentricTarget.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B)),
                                          LE.le.{0} marginFloor (Erdos390.Full.PaperGuardCensus.BarycentricTarget.cellMassMargin.{u_1} T) →
                                            ∀
                                              (hbaseline :
                                                Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1, 0} B) (Erdos390.Full.PaperGuardCensus.BarycentricTarget.baseline.{u_1} T))
                                              (z : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B))
                                              (hz : Membership.mem.{u_1, u_1} (Metric.closedBall.{u_1} (0 : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) (↑a : Real)) z),
                                              let xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B :=
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.effectiveParamEquiv.{u_1, 0} B :
                                                    (a : ↥(Erdos390.Full.PaperBridgeFit.BridgeData.EffectiveParamSpace.{u_1, 0} B)) → Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, 0} B)
                                                  z;
                                              let gamma := Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma.{u_1, 0} B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T;
                                              have hgamma :
                                                LT.lt.{0} (0 : Real)
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma.{u_1, 0} B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T) :=
                                                Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGamma_pos.{u_1, 0} B I U (HMul.hMul.{0, 0, 0} (3 : Real) (↑a : Real)) T;
                                              have hgap :
                                                ∀ (v : Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, 0} B),
                                                  LE.le.{0} (HMul.hMul.{0, 0, 0} gamma (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} v) (2 : Nat)))
                                                    (Inner.inner.{0, u_1} Real v
                                                      ((Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceCovarianceOperator.{u_1, 0} B xi :
                                                          (a : Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, 0} B) → Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, 0} B)
                                                        v)) :=
                                                fun (v : Erdos390.Full.PaperBridgeFit.BridgeData.NuisanceSpace.{u_1, 0} B) =>
                                                id.{0}
                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.canonicalEffectiveNuisanceGap_on_closedBall.{u_1, 0} B I a hU hlowerOne hupperU
                                                    (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                      Eq.mpr.{0}
                                                        (id.{0}
                                                          (congrArg.{u_1 + 1, 1} (β := Prop)
                                                            (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                              Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1} _a sigma)
                                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                            hcanonical))
                                                        (Eq.refl.{1}
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{u_1}
                                                            (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                              Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                              (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))) hsep
                                                              hremaining)
                                                            sigma)))
                                                    (fun (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign) =>
                                                      Eq.mpr.{0}
                                                        (id.{0}
                                                          (congrArg.{u_1 + 1, 1} (β := Prop)
                                                            (fun (_a : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{u_1} Head) =>
                                                              Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} _a sigma)
                                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} _a)))
                                                            hcanonical))
                                                        (Eq.refl.{1}
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                                            (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{u_1} Phead I (W :=
                                                              Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
                                                              (ledger (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))) hsep
                                                              hremaining)
                                                            sigma)))
                                                    T hbaseline hBWlarge z hz v);
                                              ∀ (b : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat)) → Real) (mu : Real),
                                                LE.le.{0}
                                                  (HMul.hMul.{0, 0, 0} kappa
                                                    (Erdos390.Lemma84.WeightedBandData.bandNormSq.{0, 0}
                                                      (Erdos390.Full.ArithmeticBandGeometry.Partition.data.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B))
                                                      (Erdos390.Lemma84.WeightedBandData.gaugePart.{0, 0}
                                                        (Erdos390.Full.ArithmeticBandGeometry.Partition.data.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)) b)))
                                                  (Erdos390.Full.FiniteProbability.covariance.{u_1} (Erdos390.Full.PaperBridgeFit.BridgeData.tiltedLaw.{u_1, 0} B xi)
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidualScore.{u_1, 0} B xi hgamma hgap
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.primeValuationScore.{u_1, 0} B
                                                        (Erdos390.Lemma84.WeightedBandData.residual.{0, 0}
                                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.data.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)) b mu)))
                                                    (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceResidualScore.{u_1, 0} B xi hgamma hgap
                                                      (Erdos390.Full.PaperBridgeFit.BridgeData.primeValuationScore.{u_1, 0} B
                                                        (Erdos390.Lemma84.WeightedBandData.residual.{0, 0}
                                                          (Erdos390.Full.ArithmeticBandGeometry.Partition.data.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.partition.{u_1, 0} B)) b mu)))))


