-- Prove2me | Definitions.Def_erdos390_analytic_compact_goals_003
-- name    : erdos390_analytic_compact_goals_003
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T16:26:16.874862+00:00
-- url     : https://prove2.me/theorems/62d8ef96-5239-4626-b9b8-ae05e25aaada
-- title:
--   Explicit propositions for four analytic comparison estimates
-- statement:
--   This file names two fully quantified power-correction comparison propositions: the actual versus medium-only comparison under fixed weights, and the weighted medium-reference versus canonical-raw comparison. Each name expands definitionally to its original quantified proposition, preserving every hypothesis and universe parameter. These definitions assert no new mathematical facts or axioms.
-- source:
--   https://github.com/ShouqiaoW/erdos/tree/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean

import Definitions.Def_erdos390_analytic_foundations_001
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_dickman_step_function
import Definitions.Def_erdos390_source_bank_interface
import Mathlib
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_MediumPNT

universe u_1 u_2
set_option maxRecDepth 10000
set_option maxHeartbeats 0

noncomputable def Erdos390.AnalyticCompactBatch003Goal001 : Prop :=
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : @Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3)
  [inst_4 : Nonempty.{u_1 + 1} Head]
  (xi : @Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)
  (rho : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head → Real) {A Aphys Kphys G : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) A →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Aphys →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Kphys →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) G →
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3
                  B)) →
            (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (rho c)) →
              (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                  @LE.le.{0} Real Real.instLE
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (rho c)
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B)
                          (@Prod.snd.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign c))))
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Finset.card.{0} Nat
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.cellFinset.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B)
                          c)))) →
                (∀
                    (r :
                      Erdos390.Full.ArithmeticBandGeometry.BandPrime
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B))
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B))),
                    @LE.le.{0} Real Real.instLE
                      (@abs.{0} Real Real.lattice Real.instAddGroup
                        (@Erdos390.Full.PaperBridgeFit.BridgeData.effectivePrimeCoefficient.{u_1, u_2} Head Band inst
                          inst_1 inst_2 inst_3 B xi r))
                      A) →
                  @LE.le.{0}
                      ((fun
                            (x :
                              @Erdos390.Full.PaperBridgeFit.BridgeData.Coord.{u_1, u_2} Head Band inst inst_1 inst_2
                                inst_3 B) =>
                          Real)
                        (@Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{u_2, u_1}
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.GaugeIndex.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B)
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B)))
                      Real.instLE
                      (@abs.{0}
                        ((fun
                              (x :
                                @Erdos390.Full.PaperBridgeFit.BridgeData.Coord.{u_1, u_2} Head Band inst inst_1 inst_2
                                  inst_3 B) =>
                            Real)
                          (@Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{u_2, u_1}
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.GaugeIndex.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B)
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B)))
                        Real.lattice Real.instAddGroup
                        (@WithLp.ofLp.{max u_1 u_2}
                          (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          ((i :
                              @Erdos390.Full.PaperBridgeFit.BridgeData.Coord.{u_1, u_2} Head Band inst inst_1 inst_2
                                inst_3 B) →
                            (fun
                                  (x :
                                    @Erdos390.Full.PaperBridgeFit.BridgeData.Coord.{u_1, u_2} Head Band inst inst_1
                                      inst_2 inst_3 B) =>
                                Real)
                              i)
                          xi
                          (@Erdos390.Full.PaperBridgeFit.MomentCoord.physical.{u_2, u_1}
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.GaugeIndex.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B)
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.HeadIndex.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B))))
                      Aphys →
                    (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                        (m :
                          @Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1} Head inst
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B)
                            c),
                        @LE.le.{0} Real Real.instLE
                          (@abs.{0} Real Real.lattice Real.instAddGroup
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.physicalScore.{u_1, u_2} Head Band inst inst_1
                              inst_2 inst_3 B
                              (@Sigma.mk.{u_1, 0} (Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                c m)))
                          Kphys) →
                      @LE.le.{0} Real Real.instLE
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Aphys Kphys)
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3
                                B)))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                        (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                            @LE.le.{0} Real Real.instLE
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (Real.exp
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) A
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} Head Band inst inst_1
                                          inst_2 inst_3 B))
                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                        (Real.log
                                          (@Nat.cast.{0} Real Real.instNatCast
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B)
                                              (@Prod.snd.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign c))))
                                        (Real.log
                                          (@Nat.cast.{0} Real Real.instNatCast
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                                inst inst_1 inst_2 inst_3 B))))))))
                                (rho c))
                              G) →
                          ∀
                            (p :
                              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))),
                            @LE.le.{0} Real Real.instLE
                              (@Finset.sum.{0, 0}
                                (Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B)))
                                Real Real.instAddCommMonoid
                                (@Finset.univ.{0}
                                  (Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B)))
                                  (@Erdos390.Full.ArithmeticBandGeometry.Partition.instFintypeBandPrime
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))))
                                fun
                                  (q :
                                    Erdos390.Full.ArithmeticBandGeometry.BandPrime
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_2 inst_3 B))
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                          inst_1 inst_2 inst_3 B))) =>
                                @abs.{0} Real Real.lattice Real.instAddGroup
                                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                      (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{u_1} Head
                                          inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleEndpoint.{u_1, u_2} Head Band
                                          inst inst_1 inst_2 inst_3 B)
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} Head
                                          Band inst inst_1 inst_2 inst_3 B inst_4 xi)
                                        (@Subtype.val.{1} Nat
                                          (fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (Erdos390.Full.ArithmeticModel.primeBand
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B)))
                                              p)
                                          p)
                                        (@Subtype.val.{1} Nat
                                          (fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (Erdos390.Full.ArithmeticModel.primeBand
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B)))
                                              p)
                                          q))
                                      (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{u_1} Head
                                          inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleEndpoint.{u_1, u_2} Head Band
                                          inst inst_1 inst_2 inst_3 B)
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} Head
                                          Band inst inst_1 inst_2 inst_3 B inst_4 xi)
                                        (@Subtype.val.{1} Nat
                                          (fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (Erdos390.Full.ArithmeticModel.primeBand
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B)))
                                              p)
                                          p)
                                        (@Subtype.val.{1} Nat
                                          (fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (Erdos390.Full.ArithmeticModel.primeBand
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B)))
                                              p)
                                          q)))
                                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                      (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{u_1} Head
                                          inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleEndpoint.{u_1, u_2} Head Band
                                          inst inst_1 inst_2 inst_3 B)
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.physicalMediumReferenceLaw.{u_1, u_2}
                                          Head Band inst inst_1 inst_2 inst_3 B inst_4 xi)
                                        (@Subtype.val.{1} Nat
                                          (fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (Erdos390.Full.ArithmeticModel.primeBand
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B)))
                                              p)
                                          p)
                                        (@Subtype.val.{1} Nat
                                          (fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (Erdos390.Full.ArithmeticModel.primeBand
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B)))
                                              p)
                                          q))
                                      (@Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleFintype.{u_1} Head
                                          inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleEndpoint.{u_1, u_2} Head Band
                                          inst inst_1 inst_2 inst_3 B)
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.physicalMediumReferenceLaw.{u_1, u_2}
                                          Head Band inst inst_1 inst_2 inst_3 B inst_4 xi)
                                        (@Subtype.val.{1} Nat
                                          (fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (Erdos390.Full.ArithmeticModel.primeBand
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B)))
                                              p)
                                          p)
                                        (@Subtype.val.{1} Nat
                                          (fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              (Erdos390.Full.ArithmeticModel.primeBand
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B))
                                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                    Band inst inst_1 inst_2 inst_3 B)))
                                              p)
                                          q)))))
                              (Erdos390.Full.PaperBridgeFit.BridgeData.physicalPowerCorrectionMixtureBudget
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Aphys Kphys)
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} Head Band inst inst_1 inst_2
                                    inst_3 B))
                                G
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                    inst_2 inst_3 B))
                                (@Subtype.val.{1} Nat
                                  (fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      (Erdos390.Full.ArithmeticModel.primeBand
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B))
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                            inst_1 inst_2 inst_3 B)))
                                      p)
                                  p))

noncomputable def Erdos390.AnalyticCompactBatch003Goal002 : Prop :=
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
        ∀ {Kscore Cenv : Real},
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Cenv →
            (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head)
                (m :
                  @Subtype.{1} Nat fun (x : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                      (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B))
                        c)
                      x),
                @LE.le.{0} Real Real.instLE
                  (@abs.{0} Real Real.lattice Real.instAddGroup
                    (Erdos390.Full.ValuationScoreDomination.valuationScore
                      (Erdos390.Full.ArithmeticModel.primeBand
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B))
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                            inst_3 B)))
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.effectiveNatCoefficient.{u_1, u_2} Head Band inst inst_1
                        inst_2 inst_3 B xi)
                      (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} Head Band inst inst_1 inst_2 inst_3 B)
                      (@Subtype.val.{1} Nat
                        (fun (x : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                            (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              c)
                            x)
                        m)))
                  Kscore) →
              (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                  @LE.le.{0} Real Real.instLE
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (Real.exp
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            Kscore))
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@Finset.card.{0} Nat
                            (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                  inst_2 inst_3 B))
                              Cprom Cbank G))))
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Finset.card.{0} Nat
                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            c))))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
                (∀ (c : Erdos390.Full.PaperBridgeFit.Cell.{u_1} Head),
                    @LE.le.{0} Real Real.instLE
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (Erdos390.Full.PaperScaleMarkedCell.paperCellDensity
                            (P (@Prod.fst.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign c))
                            (I.lower (@Prod.snd.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign c))
                            (I.upper (@Prod.snd.{u_1, 0} Head Erdos390.Full.PaperBridgeFit.PhysicalSign c)))
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))))
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Finset.card.{0} Nat
                          (@Erdos390.Full.PaperGuardCensus.rawCell.{u_1} Head P I
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))
                            c)))) →
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
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Cenv
                          (Erdos390.Full.Scale.L
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1
                                inst_2 inst_3 B))))) →
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
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@Subtype.val.{1} Nat
                              (fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                  (Erdos390.Full.ArithmeticModel.primeBand
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B))
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                        inst_1 inst_2 inst_3 B)))
                                  p)
                              p))
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
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1} Head inst
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst
                                      inst_1 inst_2 inst_3 B))) =>
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
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                  Band inst inst_1 inst_2 inst_3 B))
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
                                        (@SDiff.sdiff.{0} (Finset.{0} Nat)
                                          (@Finset.instSDiff.{0} Nat instDecidableEqNat)
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
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
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
                                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head
                                                  Band inst inst_1 inst_2 inst_3 B))
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
                                        (@SDiff.sdiff.{0} (Finset.{0} Nat)
                                          (@Finset.instSDiff.{0} Nat instDecidableEqNat)
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
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band
                                              inst inst_1 inst_2 inst_3 B))
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
                                      q))))))
                        (Erdos390.Full.PaperBridgeFit.BridgeData.guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.canonicalGuardPerturbationConstant.{u_1} Head inst P
                            I Kscore)
                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1} Head inst
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} Head Band inst inst_1 inst_2
                              inst_3 B)))


