-- Prove2me | Definitions.Def_erdos390_remaining_analytic_propositions_006
-- name    : erdos390_remaining_analytic_propositions_006
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T16:42:00.616988+00:00
-- url     : https://prove2.me/theorems/12bb9dd5-4d66-4848-a849-0db7a5653eb6
-- title:
--   Analytic construction propositions, part 6
-- statement:
--   Named propositions for the remaining analytic and finite construction estimates in the Erdős 390 central-anchor proof. Each name expands to the complete quantified statement, including every hypothesis and universe parameter. These definitions introduce no assertion of the propositions; their proofs are submitted separately. This part includes the following source declarations: exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstRichSourceWithFixedNumericalData.
-- source:
--   https://github.com/ShouqiaoW/erdos/tree/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean

import Definitions.Def_erdos390_analytic_foundations_001
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Definitions.Def_erdos390_analytic_foundations_010
import Definitions.Def_erdos390_dickman_step_function
import Definitions.Def_erdos390_source_bank_interface
import Mathlib
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_MediumPNT
set_option maxRecDepth 10000
set_option maxHeartbeats 0


noncomputable def Erdos390.RemainingAnalyticGoal006_001 : Prop :=
∀ {c deltaStar betaProt betaAct : Real} {depth N W K0 : Nat},
  LT.lt.{0} Erdos390.WholePaper.C0 c →
    Erdos390.WholePaper.IsPaperCombinedChargeDeltaStar c deltaStar →
      LT.lt.{0} (0 : Nat) W →
        LE.le.{0} (0 : Real) betaProt →
          LT.lt.{0} (0 : Real) betaAct →
            LE.le.{0} (HAdd.hAdd.{0, 0, 0} betaProt betaAct) (HDiv.hDiv.{0, 0, 0} c (Erdos390.WholePaper.roughHeadDensity W)) →
              LE.le.{0} (HDiv.hDiv.{0, 0, 0} (1 : Real) (Erdos390.WholePaper.roughHeadDensity W)) (↑(HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) : Real) →
                LE.le.{0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) depth) (1 : Nat)) W →
                  ∀ (F : Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily c depth N),
                    (∀ (n : Nat) (hn : LE.le.{0} N n),
                        have R := Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization F n hn;
                        have certificate := Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.certificate F n hn;
                        And
                          (Dvd.dvd.{0}
                            (HMul.hMul.{0, 0, 0}
                              (Erdos390.WholePaper.centralAnchorDivisor n (Erdos390.WholePaper.centralAnchorCutoff depth n) (Erdos390.WholePaper.GuardedCentralAnchorCertificate.q certificate))
                              (Erdos390.WholePaper.BankPaperRealization.prechargeBaseStateProduct R))
                            (Erdos390.WholePaper.centralTailProduct n (Erdos390.WholePaper.upperTailLength c n)))
                          (And
                            (Dvd.dvd.{0} (Finset.prod.{0, 0} (Erdos390.WholePaper.baseBankFactors.{0} (Erdos390.WholePaper.BankPaperRealization.exactificationState R)) id.{1})
                              (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget certificate))
                            (And
                              (Dvd.dvd.{0} (Erdos390.WholePaper.BankPaperRealization.selectorTailCharge R (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R deltaStar))
                                (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget certificate))
                              (And
                                (∀ (p : Nat),
                                  Membership.mem.{0, 0} (Erdos390.WholePaper.primesUpTo (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) depth) (1 : Nat))) p →
                                    LE.le.{0}
                                      (HAdd.hAdd.{0, 0, 0}
                                        (HMul.hMul.{0, 0, 0}
                                          (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} c Erdos390.WholePaper.C0) (HMul.hMul.{0, 0, 0} (24 : Real) (↑(HSub.hSub.{0, 0, 0} p (1 : Nat)) : Real)))
                                          (Erdos390.WholePaper.secondOrderScale n))
                                        (↑((Nat.factorization
                                                  (Erdos390.WholePaper.BankPaperRealization.selectorTailCharge R (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R deltaStar)) :
                                                (a : Nat) → Nat)
                                              p) :
                                          Real))
                                      (↑((Nat.factorization (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget certificate) : (a : Nat) → Nat) p) : Real))
                                (And
                                  (Eq.{1}
                                    (HMul.hMul.{0, 0, 0}
                                      (Erdos390.WholePaper.GuardedCentralAnchorCertificate.selectorTailTarget certificate R
                                        (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R deltaStar))
                                      (Erdos390.WholePaper.BankPaperRealization.selectorTailCharge R (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R deltaStar)))
                                    (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget certificate))
                                  (Eq.{1}
                                    (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget certificate)
                                      (Erdos390.WholePaper.centralAnchorDivisor n (Erdos390.WholePaper.centralAnchorCutoff depth n)
                                        (Erdos390.WholePaper.GuardedCentralAnchorCertificate.q certificate)))
                                    (Erdos390.WholePaper.centralTailProduct n (Erdos390.WholePaper.upperTailLength c n)))))))) →
                      ∀ (cSource cUpper : Real) (E : Nat) (sourceCellMargin : Real),
                        LT.lt.{0} (0 : Real) cSource →
                          LT.lt.{0} (0 : Real) cUpper →
                            LT.lt.{0} (0 : Nat) E →
                              Eq.{1} sourceCellMargin
                                  (HMul.hMul.{0, 0, 0}
                                    (Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightHeadMargin (P := Erdos390.WholePaper.primesUpTo W) E
                                      (fun (x : ↥(Erdos390.WholePaper.primesUpTo W)) => Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W) cUpper)
                                    (Erdos390.Full.PaperGuardCensus.PhysicalInterpolationTarget.tau Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget)) →
                                LE.le.{0}
                                    (HMul.hMul.{0, 0, 0} (2 : Real)
                                      (∑ p : ↥(Erdos390.WholePaper.primesUpTo W), Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient c (↑p : Nat)))
                                    (HMul.hMul.{0, 0, 0} (↑E : Real) (HDiv.hDiv.{0, 0, 0} cSource (4 : Real))) →
                                  (∀ᶠ (n : Nat) in Filter.atTop.{0},
                                      And
                                        (LE.le.{0} (HMul.hMul.{0, 0, 0} cSource (Erdos390.WholePaper.secondOrderScale n))
                                          (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass F W (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) betaAct deltaStar n))
                                        (LE.le.{0} (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass F W (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) betaAct deltaStar n)
                                          (HMul.hMul.{0, 0, 0} cUpper (Erdos390.WholePaper.secondOrderScale n)))) →
                                    ∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) (hdelta : LT.lt.{0} (0 : Real) delta),
                                      let P := Erdos390.WholePaper.primesUpTo W;
                                      let I := Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals;
                                      have Patterns := Erdos390.Full.PaperHeadSimplex.pattern P (Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W) E;
                                      have G := Erdos390.WholePaper.roughCanonicalBridgeRelevantLedgerFamily depth;
                                      have hw := add_pos.{0} hdelta (LT.lt.trans_le.{0} (Erdos390.Full.RegularRelativeMesh.Mesh.ratio_pos M) (Erdos390.Full.RegularRelativeMesh.Mesh.ratio_le_eta M));
                                      let RichFiber :=
                                        (D : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)) ×'
                                          (_ : LE.le.{0} N (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) ×'
                                            (_ : LT.lt.{0} (1 : Nat) (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) ×'
                                              (_ : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D) (0 : Nat)) ×'
                                                (_ :
                                                  Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D)) ×'
                                                  (_ :
                                                    ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                      Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                        (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                    (_ :
                                                      ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                        Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                          (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                      Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P;
                                      let ThinFiber :=
                                        (B : Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) ×
                                          Prod.{0, 0}
                                            (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                            (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B));
                                      have thinOfRich : (Z : RichFiber) → ThinFiber := fun (Z : RichFiber) =>
                                        id.{1}
                                          (fun
                                              (Z :
                                                (D : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)) ×'
                                                  (_ : LE.le.{0} N (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) ×'
                                                    (_ : LT.lt.{0} (1 : Nat) (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) ×'
                                                      (_ : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D) (0 : Nat)) ×'
                                                        (_ :
                                                          Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D)) ×'
                                                          (_ :
                                                            ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                              Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                            (_ :
                                                              ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                              Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) =>
                                            PSigma.casesOn.{1, 1, 1} (β := fun (D : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)) =>
                                              (_ : LE.le.{0} N (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) ×'
                                                (_ : LT.lt.{0} (1 : Nat) (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) ×'
                                                  (_ : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D) (0 : Nat)) ×'
                                                    (_ :
                                                      Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D)) ×'
                                                      (_ :
                                                        ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                            (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                        (_ :
                                                          ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                            Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                              (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                          Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P)
                                              (motive :=
                                              fun
                                                (x :
                                                  (D : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)) ×'
                                                    (_ : LE.le.{0} N (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) ×'
                                                      (_ : LT.lt.{0} (1 : Nat) (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) ×'
                                                        (_ : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D) (0 : Nat)) ×'
                                                          (_ :
                                                            Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D)) ×'
                                                            (_ :
                                                              ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                              (_ :
                                                                ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                  Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                                    (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                                Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) =>
                                              ThinFiber) Z
                                              fun (D : Erdos390.Full.PaperBridgeFit.StructuredSampleData.{0} (Erdos390.Full.PaperHeadSimplex.Tag P))
                                                (snd :
                                                  (_ : LE.le.{0} N (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) ×'
                                                    (_ : LT.lt.{0} (1 : Nat) (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) ×'
                                                      (_ : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D) (0 : Nat)) ×'
                                                        (_ :
                                                          Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D)) ×'
                                                          (_ :
                                                            ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                              Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                            (_ :
                                                              ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                              Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) =>
                                              PSigma.casesOn.{1, 0, 1} (β := fun (_hnTail : LE.le.{0} N (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) =>
                                                (_ : LT.lt.{0} (1 : Nat) (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) ×'
                                                  (_ : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D) (0 : Nat)) ×'
                                                    (_ :
                                                      Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D)) ×'
                                                      (_ :
                                                        ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                            (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                        (_ :
                                                          ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                            Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                              (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                          Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P)
                                                (motive :=
                                                fun
                                                  (x :
                                                    (_ : LE.le.{0} N (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) ×'
                                                      (_ : LT.lt.{0} (1 : Nat) (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) ×'
                                                        (_ : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D) (0 : Nat)) ×'
                                                          (_ :
                                                            Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D)) ×'
                                                            (_ :
                                                              ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                              (_ :
                                                                ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                  Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                                    (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                                Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) =>
                                                ThinFiber) snd
                                                fun (hnTail : LE.le.{0} N (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))
                                                  (snd :
                                                    (_ : LT.lt.{0} (1 : Nat) (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) ×'
                                                      (_ : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D) (0 : Nat)) ×'
                                                        (_ :
                                                          Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D)) ×'
                                                          (_ :
                                                            ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                              Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                            (_ :
                                                              ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                              Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) =>
                                                PSigma.casesOn.{1, 0, 1} (β := fun (_hnD : LT.lt.{0} (1 : Nat) (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) =>
                                                  (_ : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D) (0 : Nat)) ×'
                                                    (_ :
                                                      Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D)) ×'
                                                      (_ :
                                                        ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                            (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                        (_ :
                                                          ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                            Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                              (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                          Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P)
                                                  (motive :=
                                                  fun
                                                    (x :
                                                      (_ : LT.lt.{0} (1 : Nat) (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)) ×'
                                                        (_ : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D) (0 : Nat)) ×'
                                                          (_ :
                                                            Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D)) ×'
                                                            (_ :
                                                              ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                              (_ :
                                                                ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                  Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                                    (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                                Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) =>
                                                  ThinFiber) snd
                                                  fun (hnD : LT.lt.{0} (1 : Nat) (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))
                                                    (snd :
                                                      (_ : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D) (0 : Nat)) ×'
                                                        (_ :
                                                          Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D)) ×'
                                                          (_ :
                                                            ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                              Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                            (_ :
                                                              ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                              Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) =>
                                                  PSigma.casesOn.{1, 0, 1} (β := fun (_hWD : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D) (0 : Nat)) =>
                                                    (_ :
                                                      Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D)) ×'
                                                      (_ :
                                                        ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                            (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                        (_ :
                                                          ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                            Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                              (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                          Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P)
                                                    (motive :=
                                                    fun
                                                      (x :
                                                        (_ : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D) (0 : Nat)) ×'
                                                          (_ :
                                                            Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D)) ×'
                                                            (_ :
                                                              ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                              (_ :
                                                                ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                  Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                                    (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                                Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) =>
                                                    ThinFiber) snd
                                                    fun (hWD : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D) (0 : Nat))
                                                      (snd :
                                                        (_ :
                                                          Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D)) ×'
                                                          (_ :
                                                            ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                              Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                            (_ :
                                                              ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                              Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) =>
                                                    PSigma.casesOn.{1, 0, 1} (β :=
                                                      fun
                                                        (_S :
                                                          Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D)) =>
                                                      (_ :
                                                        ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                            (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                        (_ :
                                                          ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                            Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                              (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                          Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P)
                                                      (motive :=
                                                      fun
                                                        (x :
                                                          (_ :
                                                            Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D)) ×'
                                                            (_ :
                                                              ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                              (_ :
                                                                ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                  Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                                    (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                                Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) =>
                                                      ThinFiber) snd
                                                      fun
                                                        (S :
                                                          Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} D))
                                                        (snd :
                                                          (_ :
                                                            ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                              Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                            (_ :
                                                              ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                              Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) =>
                                                      PSigma.casesOn.{1, 0, 1} (β :=
                                                        fun
                                                          (_hlo :
                                                            ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                              Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) =>
                                                        (_ :
                                                          ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                            Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                              (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                          Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P)
                                                        (motive :=
                                                        fun
                                                          (x :
                                                            (_ :
                                                              ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                              (_ :
                                                                ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                  Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                                    (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                                Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) =>
                                                        ThinFiber) snd
                                                        fun
                                                          (hlo :
                                                            ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                              Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} D sigma)
                                                                (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)))
                                                          (snd :
                                                            (_ :
                                                              ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                              Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) =>
                                                        PSigma.casesOn.{1, 0, 1} (β :=
                                                          fun
                                                            (_hhi :
                                                              ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) =>
                                                          Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) (motive :=
                                                          fun
                                                            (x :
                                                              (_ :
                                                                ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                  Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                                    (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D))) ×'
                                                                Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) =>
                                                          ThinFiber) snd
                                                          fun
                                                            (hhi :
                                                              ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                                Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} D sigma)
                                                                  (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)))
                                                            (Rhead : Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P) =>
                                                          have Kphysical := Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget;
                                                          have Tsource := Erdos390.WholePaper.bankPaperCanonicalSectionNineCoherentSourceTarget M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw;
                                                          let Bsource := Erdos390.WholePaper.bankPaperCanonicalSectionNineCoherentSourceBridge M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw;
                                                          Sigma.mk.{0, 0} (β :=
                                                            fun
                                                              (B :
                                                                Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                  (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                            Prod.{0, 0}
                                                              (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                              (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                            Bsource
                                                            (id.{1}
                                                              (Prod.mk.{0, 0}
                                                                (Sigma.mk.{0, 0} (β :=
                                                                  fun
                                                                    (R :
                                                                      Erdos390.WholePaper.BankPaperRealization (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                                        (Erdos390.WholePaper.upperEndpoint (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                                          (Erdos390.WholePaper.upperTailLength c (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)))) =>
                                                                  Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                                    (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R) (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
                                                                    (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
                                                                  (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.realization F (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                                    hnTail)
                                                                  (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.certificate F (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} D)
                                                                    hnTail))
                                                                Tsource)))
                                          Z;
                                      ∃ (sourceGeom : (n : Nat) → LE.le.{0} N n → RichFiber) (source : (n : Nat) → LE.le.{0} N n → ThinFiber),
                                        And (∀ (n : Nat) (hn : LE.le.{0} N n), Eq.{1} (source n hn) (thinOfRich (sourceGeom n hn)))
                                          (And
                                            (∀ᶠ (n : Nat) in Filter.atTop.{0},
                                              ∀ (hn : LE.le.{0} N n),
                                                let X := source n hn;
                                                let B :=
                                                  Sigma.fst.{0, 0} (β :=
                                                    fun
                                                      (B :
                                                        Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P) (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                    Prod.{0, 0}
                                                      (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                      (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                    X;
                                                let R :=
                                                  Sigma.fst.{0, 0} (β :=
                                                    fun
                                                      (R :
                                                        Erdos390.WholePaper.BankPaperRealization
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                              (Sigma.fst.{0, 0} (β :=
                                                                fun
                                                                  (B :
                                                                    Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                      (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                Prod.{0, 0}
                                                                  (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                  (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                X)))
                                                          (Erdos390.WholePaper.upperEndpoint
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                (Sigma.fst.{0, 0} (β :=
                                                                  fun
                                                                    (B :
                                                                      Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                        (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                  Prod.{0, 0}
                                                                    (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                    (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                  X)))
                                                            (Erdos390.WholePaper.upperTailLength c
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                  (Sigma.fst.{0, 0} (β :=
                                                                    fun
                                                                      (B :
                                                                        Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                          (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                    Prod.{0, 0}
                                                                      (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                      (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                    X)))))) =>
                                                    Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                          (Sigma.fst.{0, 0} (β :=
                                                            fun
                                                              (B :
                                                                Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                  (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                            Prod.{0, 0}
                                                              (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                              (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                            X)))
                                                      (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R) (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
                                                      (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
                                                    (Sigma.snd.{0, 0} (β :=
                                                        fun
                                                          (B :
                                                            Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                              (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                        Prod.{0, 0}
                                                          (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                          (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                        X).1;
                                                have certificate :=
                                                  Sigma.snd.{0, 0} (β :=
                                                    fun
                                                      (R :
                                                        Erdos390.WholePaper.BankPaperRealization
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                              (Sigma.fst.{0, 0} (β :=
                                                                fun
                                                                  (B :
                                                                    Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                      (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                Prod.{0, 0}
                                                                  (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                  (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                X)))
                                                          (Erdos390.WholePaper.upperEndpoint
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                (Sigma.fst.{0, 0} (β :=
                                                                  fun
                                                                    (B :
                                                                      Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                        (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                  Prod.{0, 0}
                                                                    (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                    (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                  X)))
                                                            (Erdos390.WholePaper.upperTailLength c
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                  (Sigma.fst.{0, 0} (β :=
                                                                    fun
                                                                      (B :
                                                                        Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                          (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                    Prod.{0, 0}
                                                                      (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                      (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                    X)))))) =>
                                                    Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth
                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                          (Sigma.fst.{0, 0} (β :=
                                                            fun
                                                              (B :
                                                                Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                  (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                            Prod.{0, 0}
                                                              (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                              (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                            X)))
                                                      (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R) (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
                                                      (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
                                                    (Sigma.snd.{0, 0} (β :=
                                                        fun
                                                          (B :
                                                            Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                              (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                        Prod.{0, 0}
                                                          (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                          (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                        X).1;
                                                have T :=
                                                  (Sigma.snd.{0, 0} (β :=
                                                      fun
                                                        (B :
                                                          Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                            (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                      Prod.{0, 0}
                                                        (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                        (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                      X).2;
                                                have alpha := Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0, 0} B c K0 betaProt betaAct;
                                                have qTilde :=
                                                  Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass F W (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) betaAct deltaStar n;
                                                And (Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)) n)
                                                  (And (Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)) W)
                                                    (And
                                                      (Eq.{1} qTilde
                                                        (Erdos390.WholePaper.bankPaperCanonicalGuardedSmoothBaseMass R certificate deltaStar
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B))
                                                          (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) betaAct))
                                                      (And (LE.le.{0} (1 : Real) qTilde)
                                                        (And (Erdos390.Full.PaperBridgeFit.StructuredSampleData.HeadPatternsSeparated.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B))
                                                          (And
                                                            (HasSubset.Subset.{0}
                                                              (Erdos390.WholePaper.bankPaperCanonicalStructuredActiveValues.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B))
                                                              (Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedRow R certificate deltaStar (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) (1 : Nat)))
                                                            (And (And (LE.le.{0} (0 : Real) alpha) (LE.le.{0} alpha (1 : Real)))
                                                              (And
                                                                (And (LE.le.{0} (0 : Real) (HDiv.hDiv.{0, 0, 0} betaProt (Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} B)))
                                                                  (LE.le.{0} (HDiv.hDiv.{0, 0, 0} betaProt (Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, 0} B)) (1 : Real)))
                                                                (And
                                                                  (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt.{0} B (K :=
                                                                    HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) R certificate (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R deltaStar)
                                                                    T deltaStar betaProt alpha (HAdd.hAdd.{0, 0, 0} betaProt betaAct) qTilde)
                                                                  (Eq.{1} (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget certificate)
                                                                    (Erdos390.WholePaper.GuardedCentralAnchorCertificate.prechargedTailTarget
                                                                      (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.certificate F n hn))))))))))))
                                            (And
                                              (∀ᶠ (n : Nat) in Filter.atTop.{0},
                                                ∀ (hn : LE.le.{0} N n),
                                                  let X := source n hn;
                                                  let B :=
                                                    Sigma.fst.{0, 0} (β :=
                                                      fun
                                                        (B :
                                                          Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                            (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                      Prod.{0, 0}
                                                        (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                        (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                      X;
                                                  have R :=
                                                    Sigma.fst.{0, 0} (β :=
                                                      fun
                                                        (R :
                                                          Erdos390.WholePaper.BankPaperRealization
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                (Sigma.fst.{0, 0} (β :=
                                                                  fun
                                                                    (B :
                                                                      Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                        (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                  Prod.{0, 0}
                                                                    (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                    (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                  X)))
                                                            (Erdos390.WholePaper.upperEndpoint
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                  (Sigma.fst.{0, 0} (β :=
                                                                    fun
                                                                      (B :
                                                                        Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                          (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                    Prod.{0, 0}
                                                                      (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                      (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                    X)))
                                                              (Erdos390.WholePaper.upperTailLength c
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                    (Sigma.fst.{0, 0} (β :=
                                                                      fun
                                                                        (B :
                                                                          Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                            (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                      Prod.{0, 0}
                                                                        (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                        (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                      X)))))) =>
                                                      Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                            (Sigma.fst.{0, 0} (β :=
                                                              fun
                                                                (B :
                                                                  Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                    (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                              Prod.{0, 0}
                                                                (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                              X)))
                                                        (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R) (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
                                                        (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
                                                      (Sigma.snd.{0, 0} (β :=
                                                          fun
                                                            (B :
                                                              Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                          Prod.{0, 0}
                                                            (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                            (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                          X).1;
                                                  have certificate :=
                                                    Sigma.snd.{0, 0} (β :=
                                                      fun
                                                        (R :
                                                          Erdos390.WholePaper.BankPaperRealization
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                (Sigma.fst.{0, 0} (β :=
                                                                  fun
                                                                    (B :
                                                                      Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                        (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                  Prod.{0, 0}
                                                                    (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                    (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                  X)))
                                                            (Erdos390.WholePaper.upperEndpoint
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                  (Sigma.fst.{0, 0} (β :=
                                                                    fun
                                                                      (B :
                                                                        Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                          (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                    Prod.{0, 0}
                                                                      (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                      (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                    X)))
                                                              (Erdos390.WholePaper.upperTailLength c
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                    (Sigma.fst.{0, 0} (β :=
                                                                      fun
                                                                        (B :
                                                                          Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                            (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                      Prod.{0, 0}
                                                                        (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                        (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                      X)))))) =>
                                                      Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                            (Sigma.fst.{0, 0} (β :=
                                                              fun
                                                                (B :
                                                                  Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                    (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                              Prod.{0, 0}
                                                                (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                              X)))
                                                        (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R) (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
                                                        (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
                                                      (Sigma.snd.{0, 0} (β :=
                                                          fun
                                                            (B :
                                                              Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                          Prod.{0, 0}
                                                            (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                            (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                          X).1;
                                                  have T :=
                                                    (Sigma.snd.{0, 0} (β :=
                                                        fun
                                                          (B :
                                                            Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                              (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                        Prod.{0, 0}
                                                          (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                          (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                        X).2;
                                                  have target : (p : ↥(Erdos390.WholePaper.primesUpTo W)) → Real := fun (p : ↥(Erdos390.WholePaper.primesUpTo W)) =>
                                                    (↑((Nat.factorization
                                                              (Erdos390.WholePaper.GuardedCentralAnchorCertificate.selectorTailTarget certificate R
                                                                (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R deltaStar)) :
                                                            (a : Nat) → Nat)
                                                          (↑p : Nat)) :
                                                      Real);
                                                  And (Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)) n)
                                                    (And
                                                      (∀ (p : ↥(Erdos390.WholePaper.primesUpTo W)),
                                                        And
                                                          (LE.le.{0}
                                                            (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W)
                                                              (Erdos390.WholePaper.secondOrderScale n))
                                                            (target p))
                                                          (LE.le.{0} (target p)
                                                            (HMul.hMul.{0, 0, 0} (Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient c (↑p : Nat))
                                                              (Erdos390.WholePaper.secondOrderScale n))))
                                                      (∃ (_ : Ne.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)) (0 : Nat))
                                                        (_ :
                                                        Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B))
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                        (hlo :
                                                        ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B) sigma)
                                                            (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I sigma)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B))))
                                                        (hhi :
                                                        ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                                          Eq.{1} (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B) sigma)
                                                            (Erdos390.Full.ArithmeticModel.physicalBound (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I sigma)
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B))))
                                                        (Rhead : Erdos390.Full.PaperGuardCensus.HeadSimplexReserve (Erdos390.WholePaper.primesUpTo W)) (Kphysical :
                                                        Erdos390.Full.PaperGuardCensus.PhysicalInterpolationTarget I),
                                                        And (Eq.{1} (Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.exponent Rhead) E)
                                                          (And (∀ (p : ↥(Erdos390.WholePaper.primesUpTo W)), Eq.{1} (Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.target Rhead p) (target p))
                                                            (And
                                                              (Eq.{1}
                                                                (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass F W (HAdd.hAdd.{0, 0, 0} K0 (1 : Nat)) betaAct
                                                                  deltaStar n)
                                                                (Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.activeMass Rhead))
                                                              (And (LE.le.{0} sourceCellMargin (Erdos390.Full.PaperGuardCensus.BarycentricTarget.cellMassMargin.{0} T))
                                                                (Eq.{1} T (Erdos390.Full.PaperBridgeFit.BridgeData.barycentricTargetOfPaperData.{0} B I hlo hhi Rhead Kphysical))))))))
                                              (∀ᶠ (n : Nat) in Filter.atTop.{0},
                                                ∀ (hn : LE.le.{0} N n),
                                                  let X := source n hn;
                                                  let B :=
                                                    Sigma.fst.{0, 0} (β :=
                                                      fun
                                                        (B :
                                                          Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                            (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                      Prod.{0, 0}
                                                        (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                        (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                      X;
                                                  have R :=
                                                    Sigma.fst.{0, 0} (β :=
                                                      fun
                                                        (R :
                                                          Erdos390.WholePaper.BankPaperRealization
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                (Sigma.fst.{0, 0} (β :=
                                                                  fun
                                                                    (B :
                                                                      Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                        (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                  Prod.{0, 0}
                                                                    (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                    (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                  X)))
                                                            (Erdos390.WholePaper.upperEndpoint
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                  (Sigma.fst.{0, 0} (β :=
                                                                    fun
                                                                      (B :
                                                                        Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                          (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                    Prod.{0, 0}
                                                                      (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                      (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                    X)))
                                                              (Erdos390.WholePaper.upperTailLength c
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                    (Sigma.fst.{0, 0} (β :=
                                                                      fun
                                                                        (B :
                                                                          Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                            (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                      Prod.{0, 0}
                                                                        (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                        (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                      X)))))) =>
                                                      Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                            (Sigma.fst.{0, 0} (β :=
                                                              fun
                                                                (B :
                                                                  Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                    (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                              Prod.{0, 0}
                                                                (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                              X)))
                                                        (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R) (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
                                                        (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
                                                      (Sigma.snd.{0, 0} (β :=
                                                          fun
                                                            (B :
                                                              Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                          Prod.{0, 0}
                                                            (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                            (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                          X).1;
                                                  have certificate :=
                                                    Sigma.snd.{0, 0} (β :=
                                                      fun
                                                        (R :
                                                          Erdos390.WholePaper.BankPaperRealization
                                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                (Sigma.fst.{0, 0} (β :=
                                                                  fun
                                                                    (B :
                                                                      Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                        (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                  Prod.{0, 0}
                                                                    (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                    (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                  X)))
                                                            (Erdos390.WholePaper.upperEndpoint
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                  (Sigma.fst.{0, 0} (β :=
                                                                    fun
                                                                      (B :
                                                                        Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                          (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                    Prod.{0, 0}
                                                                      (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                      (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                    X)))
                                                              (Erdos390.WholePaper.upperTailLength c
                                                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                                    (Sigma.fst.{0, 0} (β :=
                                                                      fun
                                                                        (B :
                                                                          Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                            (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                                      Prod.{0, 0}
                                                                        (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                        (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                      X)))))) =>
                                                      Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth
                                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                            (Sigma.fst.{0, 0} (β :=
                                                              fun
                                                                (B :
                                                                  Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                    (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                              Prod.{0, 0}
                                                                (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                                (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                              X)))
                                                        (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R) (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
                                                        (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
                                                      (Sigma.snd.{0, 0} (β :=
                                                          fun
                                                            (B :
                                                              Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                                (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)) =>
                                                          Prod.{0, 0}
                                                            (Erdos390.WholePaper.BankPaperCanonicalGuardedTailFiber c depth
                                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                            (Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))
                                                          X).1;
                                                  ∃ (hsep :
                                                    LT.lt.{0}
                                                      (Erdos390.Full.ArithmeticModel.physicalBound
                                                        (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.upper I Erdos390.Full.PaperBridgeFit.PhysicalSign.minus) n)
                                                      (Erdos390.Full.ArithmeticModel.physicalBound
                                                        (Erdos390.Full.PaperGuardCensus.PhysicalIntervals.lower I Erdos390.Full.PaperBridgeFit.PhysicalSign.plus) n))
                                                    (hremaining :
                                                    ∀ (cell : Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)),
                                                      Finset.Nonempty.{0}
                                                        (SDiff.sdiff.{0} (Erdos390.Full.PaperGuardCensus.rawCell.{0} Patterns I n cell) (Erdos390.Full.PaperGuardCensus.Ledger.guards (G n)))),
                                                    And
                                                      (Eq.{1} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)
                                                        (Erdos390.Full.PaperGuardCensus.canonicalSampleData.{0} Patterns I (W := W) (G n) hsep hremaining))
                                                      (Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalBridgeGuardAgreement
                                                        (G (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B))) R certificate
                                                        deltaStar))))


