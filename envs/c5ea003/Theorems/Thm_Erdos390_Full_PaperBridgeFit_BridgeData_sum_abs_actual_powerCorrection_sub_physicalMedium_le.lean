-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_sum_abs_actual_powerCorrection_sub_physicalMedium_le
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_actual_powerCorrection_sub_physicalMedium_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:14:52.965785+00:00
-- url     : https://prove2.me/theorems/ee0b5b6f-8ae5-4c8b-9914-9a5719ba24da
-- title:
--   Actual versus medium-only power correction under the same weights
-- statement:
--   For a valuation law $\lambda$, put $\Delta_\lambda(p,q)=\operatorname{Cov}_\lambda(v_p,v_q)-\operatorname{Cov}_\lambda(\mathbf1_{p\mid m},\mathbf1_{q\mid m})$. Let $B$ have nonempty head set and $W>1$, and fix a tilt parameter $\xi$. Suppose positive cell densities $\rho_c$ obey $\#S_c\ge\rho_c\mathrm{hi}_c$. Let $A,A_{\rm phys},K_{\rm phys},G\ge0$ bound, respectively, every effective prime coefficient, the physical tilt coordinate, the absolute physical score, and each reciprocal-event constant $$\exp\!\left(2\frac A{B.L}\frac{\log\mathrm{hi}_c}{\log W}\right)/\rho_c\le G.$$ Assume $8A_{\rm phys}K_{\rm phys}/B.L\le1$. Then
--
--   $$\sum_q|\Delta_{\rm actual}(p,q)-\Delta_{\rm medium}(p,q)|\le\mathrm{physicalPowerCorrectionMixtureBudget}(A_{\rm phys}K_{\rm phys}/B.L,G,n,W,p).$$
--
--   The reference removes only the residual physical score, retaining the actual reweighted component probabilities.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperBridgePhysicalPowerCorrectionRow.lean#L1347-L1467

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

theorem Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_actual_powerCorrection_sub_physicalMedium_le :
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
                                  p)) := by sorry
