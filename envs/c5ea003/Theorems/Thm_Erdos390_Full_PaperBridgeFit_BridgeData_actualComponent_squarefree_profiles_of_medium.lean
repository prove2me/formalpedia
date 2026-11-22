-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_actualComponent_squarefree_profiles_of_medium
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.actualComponent_squarefree_profiles_of_medium
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:13:03.173587+00:00
-- url     : https://prove2.me/theorems/8aa8c269-f15b-4e9f-8547-4b6cb9e8e51d
-- title:
--   The physical tilt preserves a component squarefree profile
-- statement:
--   For a divisor $D$, let $M_n(D)$ denote the common paper divisibility main term; write $w_{p,r}=(r+1)/p^r$ and $w_{p,q,r,s}=w_{p,r}w_{q,s}$. Let $B$ be bridge data with nonempty head set, $W>1$, and consider one cell $c$ at parameter $\xi$. Suppose its guarded cardinality is at least $\rho$ times its upper physical endpoint, with $\rho>0$; its effective prime coefficients have absolute value at most $A\ge0$; $|\xi_{\rm physical}|\le A_{\rm phys}$ and the physical score has absolute value at most $K_{\rm phys}$, with both bounds nonnegative. Set
--   $$\varepsilon=A_{\rm phys}K_{\rm phys}/L,\qquad G=\rho^{-1}\exp\left(2\frac A L\frac{\log(\operatorname{hi}_c)}{\log W}\right),$$
--   and assume $8\varepsilon\le1$. If the medium law has pair and single squarefree profile errors $4E/(pq)$ and $2E/p$, then the full component law has those same profiles with $E$ replaced by $E+4\varepsilon G$. This accounts quantitatively for the second, physical tilt.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperActualSquarefreeReference.lean#L571-L730

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

theorem Erdos390.Full.PaperBridgeFit.BridgeData.actualComponent_squarefree_profiles_of_medium :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head) {Emedium rho A Aphys Kphys : Real},
  LE.le.{0} (0 : Real) A →
    LT.lt.{0} (1 : Nat)
        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
      LT.lt.{0} (0 : Real) rho →
        LE.le.{0}
            (HMul.hMul.{0, 0, 0} rho
              ↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) c.2))
            ↑(Finset.card.{0}
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellFinset.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) c)) →
          (∀
              (r :
                Erdos390.Full.ArithmeticBandGeometry.BandPrime
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                  (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
              LE.le.{0} (abs.{0} (Erdos390.Full.PaperBridgeFit.BridgeData.effectivePrimeCoefficient.{u_1, u_2} B xi r))
                A) →
            LE.le.{0} (0 : Real) Aphys →
              LE.le.{0} (0 : Real) Kphys →
                LE.le.{0}
                    (abs.{0}
                      (WithLp.ofLp.{max u_1 u_2} xi Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{u_2, u_1}))
                    Aphys →
                  (∀
                      (m :
                        Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) c),
                      LE.le.{0}
                        (abs.{0}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.physicalScore.{u_1, u_2} B (Sigma.mk.{u_1, 0} c m)))
                        Kphys) →
                    LE.le.{0}
                        (HMul.hMul.{0, 0, 0} (8 : Real)
                          (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} Aphys Kphys)
                            (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B)))
                        (1 : Real) →
                      (∀ (p : Nat),
                          Membership.mem.{0, 0}
                              (Erdos390.Full.ArithmeticModel.primeBand
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                              p →
                            ∀ (q : Nat),
                              Membership.mem.{0, 0}
                                  (Finset.erase.{0}
                                    (Erdos390.Full.ArithmeticModel.primeBand
                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                    p)
                                  q →
                                LE.le.{0}
                                  (abs.{0}
                                    (HSub.hSub.{0, 0, 0}
                                      (Erdos390.Full.FiniteProbability.expect.{0}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw.{u_1, u_2} B xi c)
                                        fun m =>
                                        Erdos390.Full.ArithmeticModel.divInd
                                          (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)) ↑m)
                                      (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                        (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)))))
                                  (HMul.hMul.{0, 0, 0} Emedium
                                    (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q (1 : Nat) (1 : Nat)))) →
                        (∀ (p : Nat),
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
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.cellMediumLaw.{u_1, u_2} B xi c) fun m =>
                                      Erdos390.Full.ArithmeticModel.divInd p ↑m)
                                    (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                      p)))
                                (HMul.hMul.{0, 0, 0} Emedium
                                  (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat)))) →
                          have epsilon :=
                            HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} Aphys Kphys)
                              (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B);
                          have G :=
                            HDiv.hDiv.{0, 0, 0}
                              (Real.exp
                                (HMul.hMul.{0, 0, 0} (2 : Real)
                                  (HMul.hMul.{0, 0, 0}
                                    (HDiv.hDiv.{0, 0, 0} A (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B))
                                    (HDiv.hDiv.{0, 0, 0}
                                      (Real.log
                                        ↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) c.2))
                                      (Real.log
                                        ↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))))))
                              rho;
                          And
                            (∀ (p : Nat),
                              Membership.mem.{0, 0}
                                  (Erdos390.Full.ArithmeticModel.primeBand
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                  p →
                                ∀ (q : Nat),
                                  Membership.mem.{0, 0}
                                      (Finset.erase.{0}
                                        (Erdos390.Full.ArithmeticModel.primeBand
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                        p)
                                      q →
                                    LE.le.{0}
                                      (abs.{0}
                                        (HSub.hSub.{0, 0, 0}
                                          (Erdos390.Full.FiniteProbability.expect.{0}
                                            (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.probability.{0}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                  u_2}
                                                B xi c))
                                            fun m =>
                                            Erdos390.Full.ArithmeticModel.divInd
                                              (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat))
                                              (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                    u_2}
                                                  B xi c)
                                                m))
                                          (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                            (Erdos390.Full.OmittedTiltPairChamber.pairPower p q (1 : Nat) (1 : Nat)))))
                                      (HMul.hMul.{0, 0, 0}
                                        (HAdd.hAdd.{0, 0, 0} Emedium
                                          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) epsilon) G))
                                        (Erdos390.Full.PaperPrimePowerChamberError.pairWeight p q (1 : Nat) (1 : Nat))))
                            (∀ (p : Nat),
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
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                              u_2}
                                            B xi c))
                                        fun m =>
                                        Erdos390.Full.ArithmeticModel.divInd p
                                          (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.value.{0}
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.actualComponentValuationLaw.{u_1,
                                                u_2}
                                              B xi c)
                                            m))
                                      (Erdos390.Full.PaperScaleMarkedCell.paperDivisibilityMain
                                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                                        p)))
                                  (HMul.hMul.{0, 0, 0}
                                    (HAdd.hAdd.{0, 0, 0} Emedium
                                      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) epsilon) G))
                                    (Erdos390.Full.PaperPrimePowerChamberError.singleWeight p (1 : Nat)))) := by sorry
