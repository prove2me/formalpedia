-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_eventually_bankPaperCanonicalTwoZeroHeadCell_scalarCapacity_of_asymptoticMass
-- name    : Erdos390.WholePaper.BankPaperRealization.eventually_bankPaperCanonicalTwoZeroHeadCell_scalarCapacity_of_asymptoticMass
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:20:33.941295+00:00
-- url     : https://prove2.me/theorems/1f346e8a-6fa5-4759-bdb2-dda6450b7fcd
-- title:
--   Asymptotic capacity of both zero-head cells
-- statement:
--   Fix a finite prime set and finite band type, a head-pattern map, physical intervals, and a ledger family with fixed promotion and bank parameters. Let $q_n$ have a positive lower bound of paper scale and satisfy $q_n=O(s_n)$, while $e_n=o(s_n)$, where $s_n$ is the second-order scale. Fix $\eta>0$ and any real protection parameter $\beta$. Eventually, uniformly over bridge data of size $n$ equal to the canonical sample data (with separated intervals and nonempty guarded raw cells), and all barycentric targets with cell-mass margin at least $\eta$, each sign $\sigma$ satisfies
--   $$0\le q_n\mu_{0,\sigma}+e_n\le |\mathcal S_{0,\sigma}|\left(1-\frac\beta{B.L}\right).$$
--   Here $\mu_{0,\sigma}$ is the target baseline cell mass and $\mathcal S_{0,\sigma}$ the corresponding sample cell.
--
--   This provides one capacity argument for both normalization and height-only adjustments.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSectionEightTwoZeroOneShotConnector.lean#L53-L276

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_008

universe u_1

theorem Erdos390.WholePaper.BankPaperRealization.eventually_bankPaperCanonicalTwoZeroHeadCell_scalarCapacity_of_asymptoticMass :
∀ {P : Finset.{0} Nat} {Band : Type u_1} [inst : Fintype.{u_1} Band] [inst_1 : DecidableEq.{u_1 + 1} Band]
  (Phead : Erdos390.Full.PaperHeadSimplex.Tag P → Erdos390.Full.HeadPattern.Pattern)
  (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (Cprom Cbank : Nat)
  (ledger : (n : Nat) → Erdos390.Full.PaperGuardCensus.Ledger n Cprom Cbank) (activeMass cellChange : Nat → Real),
  Erdos390.WholePaper.BankPaperCanonicalActiveMassPaperScaleLower activeMass →
    @Asymptotics.IsBigO.{0, 0, 0} Nat Real Real Real.norm Real.norm (@Filter.atTop.{0} Nat Nat.instPreorder) activeMass
        Erdos390.WholePaper.secondOrderScale →
      @Asymptotics.IsLittleO.{0, 0, 0} Nat Real Real Real.norm Real.norm (@Filter.atTop.{0} Nat Nat.instPreorder)
          cellChange Erdos390.WholePaper.secondOrderScale →
        ∀ {marginFloor : Real},
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              marginFloor →
            ∀ (betaProt : Real),
              @Filter.Eventually.{0} Nat
                (fun (n : Nat) =>
                  ∀
                    (B :
                      @Erdos390.Full.PaperBridgeFit.BridgeData.{0, u_1} (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                        (@instFintypeOption.{0}
                          (@Subtype.{1} Nat fun (p : Nat) =>
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                          (@Finset.Subtype.fintype.{0} Nat P))
                        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                          @Option.instDecidableEq.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (fun
                                (a b :
                                  @Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p) =>
                              @Subtype.instDecidableEq.{1} Nat
                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                                instDecidableEqNat a b)
                            a b)
                        inst inst_1),
                    @Eq.{1} Nat
                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                          (@instFintypeOption.{0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            (@Finset.Subtype.fintype.{0} Nat P))
                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                            (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                            (@instFintypeOption.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                              @Option.instDecidableEq.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (fun
                                    (a b :
                                      @Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p) =>
                                  @Subtype.instDecidableEq.{1} Nat
                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P)
                                    instDecidableEqNat a b)
                                a b)
                            inst inst_1 B))
                        n →
                      ∀
                        (hsep :
                          @LT.lt.{0} Nat instLTNat
                            (Erdos390.Full.ArithmeticModel.physicalBound
                              (I.upper Erdos390.Full.PaperBridgeFit.PhysicalSign.minus)
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (@Finset.Subtype.fintype.{0} Nat P))
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                  (@instFintypeOption.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (@Finset.Subtype.fintype.{0} Nat P))
                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                    @Option.instDecidableEq.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p)
                                      (fun
                                          (a b :
                                            @Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p) =>
                                        @Subtype.instDecidableEq.{1} Nat
                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P)
                                          instDecidableEqNat a b)
                                      a b)
                                  inst inst_1 B)))
                            (Erdos390.Full.ArithmeticModel.physicalBound
                              (I.lower Erdos390.Full.PaperBridgeFit.PhysicalSign.plus)
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (@Finset.Subtype.fintype.{0} Nat P))
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                  (@instFintypeOption.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (@Finset.Subtype.fintype.{0} Nat P))
                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                    @Option.instDecidableEq.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p)
                                      (fun
                                          (a b :
                                            @Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p) =>
                                        @Subtype.instDecidableEq.{1} Nat
                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P)
                                          instDecidableEqNat a b)
                                      a b)
                                  inst inst_1 B))))
                        (hremaining :
                          ∀ (cell : Erdos390.Full.PaperBridgeFit.Cell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)),
                            @Finset.Nonempty.{0} Nat
                              (@SDiff.sdiff.{0} (Finset.{0} Nat) (@Finset.instSDiff.{0} Nat instDecidableEqNat)
                                (@Erdos390.Full.PaperGuardCensus.rawCell.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                  Phead I
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                    (Erdos390.Full.PaperHeadSimplex.Tag P)
                                    (@instFintypeOption.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p)
                                      (@Finset.Subtype.fintype.{0} Nat P))
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                      (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                      (@instFintypeOption.{0}
                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p)
                                        (@Finset.Subtype.fintype.{0} Nat P))
                                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                        @Option.instDecidableEq.{0}
                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p)
                                          (fun
                                              (a b :
                                                @Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p) =>
                                            @Subtype.instDecidableEq.{1} Nat
                                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P)
                                              instDecidableEqNat a b)
                                          a b)
                                      inst inst_1 B))
                                  cell)
                                (@Erdos390.Full.PaperGuardCensus.Ledger.guards
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                    (Erdos390.Full.PaperHeadSimplex.Tag P)
                                    (@instFintypeOption.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p)
                                      (@Finset.Subtype.fintype.{0} Nat P))
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                      (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                      (@instFintypeOption.{0}
                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p)
                                        (@Finset.Subtype.fintype.{0} Nat P))
                                      (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                        @Option.instDecidableEq.{0}
                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p)
                                          (fun
                                              (a b :
                                                @Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p) =>
                                            @Subtype.instDecidableEq.{1} Nat
                                              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P)
                                              instDecidableEqNat a b)
                                          a b)
                                      inst inst_1 B))
                                  Cprom Cbank
                                  (ledger
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                      (Erdos390.Full.PaperHeadSimplex.Tag P)
                                      (@instFintypeOption.{0}
                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p)
                                        (@Finset.Subtype.fintype.{0} Nat P))
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                        (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                        (@instFintypeOption.{0}
                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p)
                                          (@Finset.Subtype.fintype.{0} Nat P))
                                        (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                          @Option.instDecidableEq.{0}
                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p)
                                            (fun
                                                (a b :
                                                  @Subtype.{1} Nat fun (p : Nat) =>
                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P p) =>
                                              @Subtype.instDecidableEq.{1} Nat
                                                (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P)
                                                instDecidableEqNat a b)
                                            a b)
                                        inst inst_1 B)))))),
                        @Eq.{1}
                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.{0}
                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P)))
                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                @Option.instDecidableEq.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (fun
                                      (a b :
                                        @Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p) =>
                                    @Subtype.instDecidableEq.{1} Nat
                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P)
                                      instDecidableEqNat a b)
                                  a b)
                              inst inst_1 B)
                            (@Erdos390.Full.PaperGuardCensus.canonicalSampleData.{0}
                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                              (@instFintypeOption.{0}
                                (@Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                (@Finset.Subtype.fintype.{0} Nat P))
                              Phead I
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (@Finset.Subtype.fintype.{0} Nat P))
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                  (@instFintypeOption.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (@Finset.Subtype.fintype.{0} Nat P))
                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                    @Option.instDecidableEq.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p)
                                      (fun
                                          (a b :
                                            @Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p) =>
                                        @Subtype.instDecidableEq.{1} Nat
                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P)
                                          instDecidableEqNat a b)
                                      a b)
                                  inst inst_1 B))
                              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0}
                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (@Finset.Subtype.fintype.{0} Nat P))
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                  (@instFintypeOption.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (@Finset.Subtype.fintype.{0} Nat P))
                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                    @Option.instDecidableEq.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p)
                                      (fun
                                          (a b :
                                            @Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p) =>
                                        @Subtype.instDecidableEq.{1} Nat
                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P)
                                          instDecidableEqNat a b)
                                      a b)
                                  inst inst_1 B))
                              Cprom Cbank
                              (ledger
                                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                  (@instFintypeOption.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (@Finset.Subtype.fintype.{0} Nat P))
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                    (@instFintypeOption.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p)
                                      (@Finset.Subtype.fintype.{0} Nat P))
                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                      @Option.instDecidableEq.{0}
                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p)
                                        (fun
                                            (a b :
                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p) =>
                                          @Subtype.instDecidableEq.{1} Nat
                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P)
                                            instDecidableEqNat a b)
                                        a b)
                                    inst inst_1 B)))
                              hsep hremaining) →
                          ∀
                            (T :
                              @Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0}
                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                (@instFintypeOption.{0}
                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                        (@Finset.instSetLike.{0} Nat))
                                      P p)
                                  (@Finset.Subtype.fintype.{0} Nat P))
                                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                  (@instFintypeOption.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (@Finset.Subtype.fintype.{0} Nat P))
                                  (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                    @Option.instDecidableEq.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p)
                                      (fun
                                          (a b :
                                            @Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p) =>
                                        @Subtype.instDecidableEq.{1} Nat
                                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P)
                                          instDecidableEqNat a b)
                                      a b)
                                  inst inst_1 B)),
                            @LE.le.{0} Real Real.instLE marginFloor
                                (@Erdos390.Full.PaperGuardCensus.BarycentricTarget.cellMassMargin.{0}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                  (@instFintypeOption.{0}
                                    (@Subtype.{1} Nat fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    (@Finset.Subtype.fintype.{0} Nat P))
                                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                    (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                    (@instFintypeOption.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p)
                                      (@Finset.Subtype.fintype.{0} Nat P))
                                    (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                      @Option.instDecidableEq.{0}
                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p)
                                        (fun
                                            (a b :
                                              @Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p) =>
                                          @Subtype.instDecidableEq.{1} Nat
                                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P)
                                            instDecidableEqNat a b)
                                        a b)
                                    inst inst_1 B)
                                  T) →
                              ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                                And
                                  (@LE.le.{0} Real Real.instLE
                                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (activeMass n)
                                        (@Erdos390.Full.PaperBridgeFit.BaselineAllocation.cellMass.{0}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                          (@instFintypeOption.{0}
                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p)
                                            (@Finset.Subtype.fintype.{0} Nat P))
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                            (@instFintypeOption.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p)
                                              (@Finset.Subtype.fintype.{0} Nat P))
                                            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                              @Option.instDecidableEq.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p)
                                                (fun
                                                    (a b :
                                                      @Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p) =>
                                                  @Subtype.instDecidableEq.{1} Nat
                                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P)
                                                    instDecidableEqNat a b)
                                                a b)
                                            inst inst_1 B)
                                          (@Erdos390.Full.PaperGuardCensus.BarycentricTarget.baseline.{0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@instFintypeOption.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p)
                                              (@Finset.Subtype.fintype.{0} Nat P))
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                              (@instFintypeOption.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p)
                                                (@Finset.Subtype.fintype.{0} Nat P))
                                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                @Option.instDecidableEq.{0}
                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P p)
                                                  (fun
                                                      (a b :
                                                        @Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p) =>
                                                    @Subtype.instDecidableEq.{1} Nat
                                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P)
                                                      instDecidableEqNat a b)
                                                  a b)
                                              inst inst_1 B)
                                            T)
                                          (@Prod.mk.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            Erdos390.Full.PaperBridgeFit.PhysicalSign
                                            (@Option.none.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p))
                                            sigma)))
                                      (cellChange n)))
                                  (@LE.le.{0} Real Real.instLE
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (activeMass n)
                                        (@Erdos390.Full.PaperBridgeFit.BaselineAllocation.cellMass.{0}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                          (@instFintypeOption.{0}
                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p)
                                            (@Finset.Subtype.fintype.{0} Nat P))
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                            (@instFintypeOption.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p)
                                              (@Finset.Subtype.fintype.{0} Nat P))
                                            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                              @Option.instDecidableEq.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p)
                                                (fun
                                                    (a b :
                                                      @Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p) =>
                                                  @Subtype.instDecidableEq.{1} Nat
                                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P)
                                                    instDecidableEqNat a b)
                                                a b)
                                            inst inst_1 B)
                                          (@Erdos390.Full.PaperGuardCensus.BarycentricTarget.baseline.{0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@instFintypeOption.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p)
                                              (@Finset.Subtype.fintype.{0} Nat P))
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                              (@instFintypeOption.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p)
                                                (@Finset.Subtype.fintype.{0} Nat P))
                                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                @Option.instDecidableEq.{0}
                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P p)
                                                  (fun
                                                      (a b :
                                                        @Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p) =>
                                                    @Subtype.instDecidableEq.{1} Nat
                                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P)
                                                      instDecidableEqNat a b)
                                                  a b)
                                              inst inst_1 B)
                                            T)
                                          (@Prod.mk.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            Erdos390.Full.PaperBridgeFit.PhysicalSign
                                            (@Option.none.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p))
                                            sigma)))
                                      (cellChange n))
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@Nat.cast.{0} Real Real.instNatCast
                                        (@Fintype.card.{0}
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.SampleAt.{0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@instFintypeOption.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p)
                                              (@Finset.Subtype.fintype.{0} Nat P))
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                              (@instFintypeOption.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p)
                                                (@Finset.Subtype.fintype.{0} Nat P))
                                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                @Option.instDecidableEq.{0}
                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P p)
                                                  (fun
                                                      (a b :
                                                        @Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p) =>
                                                    @Subtype.instDecidableEq.{1} Nat
                                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P)
                                                      instDecidableEqNat a b)
                                                  a b)
                                              inst inst_1 B)
                                            (@Prod.mk.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                              Erdos390.Full.PaperBridgeFit.PhysicalSign
                                              (@Option.none.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p))
                                              sigma))
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.sampleAtFintype.{0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@instFintypeOption.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p)
                                              (@Finset.Subtype.fintype.{0} Nat P))
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, u_1}
                                              (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                              (@instFintypeOption.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p)
                                                (@Finset.Subtype.fintype.{0} Nat P))
                                              (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                                @Option.instDecidableEq.{0}
                                                  (@Subtype.{1} Nat fun (p : Nat) =>
                                                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P p)
                                                  (fun
                                                      (a b :
                                                        @Subtype.{1} Nat fun (p : Nat) =>
                                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                              (@Finset.instSetLike.{0} Nat))
                                                            P p) =>
                                                    @Subtype.instDecidableEq.{1} Nat
                                                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                          (@Finset.instSetLike.{0} Nat))
                                                        P)
                                                      instDecidableEqNat a b)
                                                  a b)
                                              inst inst_1 B)
                                            (@Prod.mk.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                                              Erdos390.Full.PaperBridgeFit.PhysicalSign
                                              (@Option.none.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p))
                                              sigma))))
                                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                          betaProt
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.L.{0, u_1}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P) Band
                                            (@instFintypeOption.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p)
                                              (@Finset.Subtype.fintype.{0} Nat P))
                                            (fun (a b : Erdos390.Full.PaperHeadSimplex.Tag P) =>
                                              @Option.instDecidableEq.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p)
                                                (fun
                                                    (a b :
                                                      @Subtype.{1} Nat fun (p : Nat) =>
                                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                            (@Finset.instSetLike.{0} Nat))
                                                          P p) =>
                                                  @Subtype.instDecidableEq.{1} Nat
                                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                        (@Finset.instSetLike.{0} Nat))
                                                      P)
                                                    instDecidableEqNat a b)
                                                a b)
                                            inst inst_1 B))))))
                (@Filter.atTop.{0} Nat Nat.instPreorder) := by sorry
