-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_bankPaperCanonicalSectionNinePostHeightBridgeInputsAt_of_preconstructedSource_and_postMargin
-- name    : Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeightBridgeInputsAt_of_preconstructedSource_and_postMargin
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:55:04.396563+00:00
-- url     : https://prove2.me/theorems/c25cef55-4a55-4c5d-9e12-260397e967d7
-- title:
--   A preconstructed source and a positive post-height margin give fresh bridge inputs
-- statement:
--   Fix a regular relative mesh of positive width, a source bridge $B$, its bank realization and guarded central-anchor certificate, and scale separation with nonzero prime cutoff. Suppose the source has the canonical post-height physical intervals and its target is the barycentric target determined by a head reserve $R_h$ and a physical interpolation target. Let $E$ be the reserve exponent, $\widetilde q$ its active mass, and $a_p$ the prime valuations of the residual selector target. Choose real $q_0,A_0,q_n,\beta_{\rm prot},\beta_{\rm act},\delta_*$, integer $d$, and margin $m>0$, with
--   $$q_n=q_0-d>0,\qquad \frac{a_p}{Eq_n}\ge m\ (p\in P),\qquad1-\sum_{p\in P}\frac{a_p}{Eq_n}\ge m.$$
--   Assume the literal rounded source mass and source height are exactly $q_0,A_0$, and that $(A_0+d\log n)/q_n$ lies between the logarithmic inner physical endpoints with distance at least half the canonical physical tolerance. Then there is a fresh post-height bridge-input package $J$ preserving the source reserve and physical target, with
--   $$J.\widetilde q=R_h.\mathrm{activeMass},\quad J.E=E,\quad J.d=d,\quad(J.q_0,J.A_0,J.q_n)=(q_0,A_0,q_n),$$
--   and the prescribed protected/active coefficients. Its head margin is exactly $m$ and its physical tolerance is half the canonical tolerance. The source's own margin is already embodied in the preconstructed reserve.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSectionNinePostHeightSourceFirstFiniteAssembly.lean#L35-L247

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
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Definitions.Def_erdos390_analytic_foundations_010

theorem Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeightBridgeInputsAt_of_preconstructedSource_and_postMargin :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) {P : Finset.{0} Nat}
  (Bsource :
    @Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
      (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
            @Subtype.instDecidableEq.{1} Nat
              (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
              instDecidableEqNat a b)
          a b)
      (Fin.fintype
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (instDecidableEqFin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  {c : Real} {depth K0 : Nat}
  (R :
    Erdos390.WholePaper.BankPaperRealization
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                @Subtype.instDecidableEq.{1} Nat
                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                  instDecidableEqNat a b)
              a b)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Bsource))
      (Erdos390.WholePaper.upperEndpoint
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperTailLength c
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource)))))
  (certificate :
    Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                @Subtype.instDecidableEq.{1} Nat
                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                  instDecidableEqNat a b)
              a b)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Bsource))
      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))))
        R)
      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))))
        R)
      (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (Erdos390.WholePaper.upperEndpoint
          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource))
          (Erdos390.WholePaper.upperTailLength c
            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))))
        R depth))
  (hdelta :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta),
  @Ne.{1} Nat
      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
        (@instFintypeOption.{0}
          (@Subtype.{1} Nat fun (p : Nat) =>
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
          (@Finset.Subtype.fintype.{0} Nat P))
        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                @Subtype.instDecidableEq.{1} Nat
                  (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                  instDecidableEqNat a b)
              a b)
          (Fin.fintype
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instDecidableEqFin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Bsource))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation delta eta M
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource))
        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
          (@instFintypeOption.{0}
            (@Subtype.{1} Nat fun (p : Nat) =>
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
            (@Finset.Subtype.fintype.{0} Nat P))
          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                  @Subtype.instDecidableEq.{1} Nat
                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                    instDecidableEqNat a b)
                a b)
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instDecidableEqFin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bsource)) →
      ∀
        (hlo :
          ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
            @Eq.{1} Nat
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.lo.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  (Fin.fintype
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Bsource)
                sigma)
              (Erdos390.Full.ArithmeticModel.physicalBound
                (Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower sigma)
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p) =>
                          @Subtype.instDecidableEq.{1} Nat
                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                            instDecidableEqNat a b)
                        a b)
                    (Fin.fintype
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (instDecidableEqFin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    Bsource))))
        (hhi :
          ∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
            @Eq.{1} Nat
              (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@instFintypeOption.{0}
                  (@Subtype.{1} Nat fun (p : Nat) =>
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                  (@Finset.Subtype.fintype.{0} Nat P))
                (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                p) =>
                        @Subtype.instDecidableEq.{1} Nat
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                          instDecidableEqNat a b)
                      a b)
                  (Fin.fintype
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Bsource)
                sigma)
              (Erdos390.Full.ArithmeticModel.physicalBound
                (Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper sigma)
                (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                  (@instFintypeOption.{0}
                    (@Subtype.{1} Nat fun (p : Nat) =>
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                    (@Finset.Subtype.fintype.{0} Nat P))
                  (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                    (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p) =>
                          @Subtype.instDecidableEq.{1} Nat
                            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                            instDecidableEqNat a b)
                        a b)
                    (Fin.fintype
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (instDecidableEqFin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    Bsource))))
        (Rhead : Erdos390.Full.PaperGuardCensus.HeadSimplexReserve P)
        (Kphysical :
          Erdos390.Full.PaperGuardCensus.PhysicalInterpolationTarget
            Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals)
        (Tsource :
          @Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
            (@instFintypeOption.{0}
              (@Subtype.{1} Nat fun (p : Nat) =>
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
              (@Finset.Subtype.fintype.{0} Nat P))
            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p) =>
                    @Subtype.instDecidableEq.{1} Nat
                      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                      instDecidableEqNat a b)
                  a b)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource)),
        @Eq.{1}
            (@Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0} (Erdos390.Full.PaperHeadSimplex.Tag P)
              (@instFintypeOption.{0}
                (@Subtype.{1} Nat fun (p : Nat) =>
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                (@Finset.Subtype.fintype.{0} Nat P))
              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                              p) =>
                      @Subtype.instDecidableEq.{1} Nat
                        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P)
                        instDecidableEqNat a b)
                    a b)
                (Fin.fintype
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (instDecidableEqFin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bsource))
            Tsource
            (@Erdos390.Full.PaperBridgeFit.BridgeData.barycentricTargetOfPaperData.{0} P
              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
              (Fin.fintype
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              Bsource Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals hlo hhi Rhead
              Kphysical) →
          ∀ (deltaStar betaProt betaAct qTilde q0 A0 qn : Real) (d : Int) (postMargin : Real),
            @Eq.{1} Real qTilde (@Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.activeMass P Rhead) →
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  qn →
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    postMargin →
                  (∀
                      (p :
                        @Subtype.{1} Nat fun (p : Nat) =>
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p),
                      @LE.le.{0} Real Real.instLE postMargin
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@DFunLike.coe.{1, 1, 1}
                              (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Nat
                              (fun (x : Nat) => Nat)
                              (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                              (@Erdos390.WholePaper.GuardedCentralAnchorCertificate.selectorTailTarget c depth
                                  (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                    (Erdos390.Full.PaperHeadSimplex.Tag P)
                                    (@instFintypeOption.{0}
                                      (@Subtype.{1} Nat fun (p : Nat) =>
                                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                            (@Finset.instSetLike.{0} Nat))
                                          P p)
                                      (@Finset.Subtype.fintype.{0} Nat P))
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                      (Erdos390.Full.PaperHeadSimplex.Tag P)
                                      (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                      (Fin.fintype
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      (instDecidableEqFin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      Bsource))
                                  (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                      (Erdos390.Full.PaperHeadSimplex.Tag P)
                                      (@instFintypeOption.{0}
                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p)
                                        (@Finset.Subtype.fintype.{0} Nat P))
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                        (Erdos390.Full.PaperHeadSimplex.Tag P)
                                        (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                        (Fin.fintype
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (instDecidableEqFin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        Bsource))
                                    (Erdos390.WholePaper.upperEndpoint
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                        (Erdos390.Full.PaperHeadSimplex.Tag P)
                                        (@instFintypeOption.{0}
                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p)
                                          (@Finset.Subtype.fintype.{0} Nat P))
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                          (Fin.fintype
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (instDecidableEqFin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          Bsource))
                                      (Erdos390.WholePaper.upperTailLength c
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                          (@instFintypeOption.{0}
                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p)
                                            (@Finset.Subtype.fintype.{0} Nat P))
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (instDecidableEqFin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Bsource))))
                                    R)
                                  (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                      (Erdos390.Full.PaperHeadSimplex.Tag P)
                                      (@instFintypeOption.{0}
                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p)
                                        (@Finset.Subtype.fintype.{0} Nat P))
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                        (Erdos390.Full.PaperHeadSimplex.Tag P)
                                        (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                        (Fin.fintype
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (instDecidableEqFin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        Bsource))
                                    (Erdos390.WholePaper.upperEndpoint
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                        (Erdos390.Full.PaperHeadSimplex.Tag P)
                                        (@instFintypeOption.{0}
                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p)
                                          (@Finset.Subtype.fintype.{0} Nat P))
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                          (Fin.fintype
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (instDecidableEqFin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          Bsource))
                                      (Erdos390.WholePaper.upperTailLength c
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                          (@instFintypeOption.{0}
                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p)
                                            (@Finset.Subtype.fintype.{0} Nat P))
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (instDecidableEqFin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Bsource))))
                                    R)
                                  (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                      (Erdos390.Full.PaperHeadSimplex.Tag P)
                                      (@instFintypeOption.{0}
                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p)
                                        (@Finset.Subtype.fintype.{0} Nat P))
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                        (Erdos390.Full.PaperHeadSimplex.Tag P)
                                        (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                        (Fin.fintype
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (instDecidableEqFin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        Bsource))
                                    (Erdos390.WholePaper.upperEndpoint
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                        (Erdos390.Full.PaperHeadSimplex.Tag P)
                                        (@instFintypeOption.{0}
                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p)
                                          (@Finset.Subtype.fintype.{0} Nat P))
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                          (Fin.fintype
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (instDecidableEqFin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          Bsource))
                                      (Erdos390.WholePaper.upperTailLength c
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                          (@instFintypeOption.{0}
                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p)
                                            (@Finset.Subtype.fintype.{0} Nat P))
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (instDecidableEqFin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Bsource))))
                                    R depth)
                                  certificate R
                                  (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors
                                    (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                      (Erdos390.Full.PaperHeadSimplex.Tag P)
                                      (@instFintypeOption.{0}
                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p)
                                        (@Finset.Subtype.fintype.{0} Nat P))
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                        (Erdos390.Full.PaperHeadSimplex.Tag P)
                                        (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                        (Fin.fintype
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (instDecidableEqFin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        Bsource))
                                    (Erdos390.WholePaper.upperTailLength c
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                        (Erdos390.Full.PaperHeadSimplex.Tag P)
                                        (@instFintypeOption.{0}
                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p)
                                          (@Finset.Subtype.fintype.{0} Nat P))
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                          (Fin.fintype
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (instDecidableEqFin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          Bsource)))
                                    R deltaStar)).factorization
                              (@Subtype.val.{1} Nat
                                (fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p)
                                p)))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@Nat.cast.{0} Real Real.instNatCast
                              (@Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.exponent P Rhead))
                            qn))) →
                    @LE.le.{0} Real Real.instLE postMargin
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@Finset.sum.{0, 0}
                            (@Subtype.{1} Nat fun (p : Nat) =>
                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P p)
                            Real Real.instAddCommMonoid
                            (@Finset.univ.{0}
                              (@Subtype.{1} Nat fun (p : Nat) =>
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) P
                                  p)
                              (@Finset.Subtype.fintype.{0} Nat P))
                            fun
                              (p :
                                @Subtype.{1} Nat fun (p : Nat) =>
                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                                    P p) =>
                            @HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@Nat.cast.{0} Real Real.instNatCast
                                (@DFunLike.coe.{1, 1, 1}
                                  (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Nat
                                  (fun (x : Nat) => Nat)
                                  (@Finsupp.instFunLike.{0, 0} Nat Nat
                                    (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                                  (@Erdos390.WholePaper.GuardedCentralAnchorCertificate.selectorTailTarget c depth
                                      (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                        (Erdos390.Full.PaperHeadSimplex.Tag P)
                                        (@instFintypeOption.{0}
                                          (@Subtype.{1} Nat fun (p : Nat) =>
                                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                (@Finset.instSetLike.{0} Nat))
                                              P p)
                                          (@Finset.Subtype.fintype.{0} Nat P))
                                        (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                          (Fin.fintype
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (instDecidableEqFin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          Bsource))
                                      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                          (@instFintypeOption.{0}
                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p)
                                            (@Finset.Subtype.fintype.{0} Nat P))
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (instDecidableEqFin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Bsource))
                                        (Erdos390.WholePaper.upperEndpoint
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@instFintypeOption.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p)
                                              (@Finset.Subtype.fintype.{0} Nat P))
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              Bsource))
                                          (Erdos390.WholePaper.upperTailLength c
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                              (@instFintypeOption.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p)
                                                (@Finset.Subtype.fintype.{0} Nat P))
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                Bsource))))
                                        R)
                                      (@Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                          (@instFintypeOption.{0}
                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p)
                                            (@Finset.Subtype.fintype.{0} Nat P))
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (instDecidableEqFin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Bsource))
                                        (Erdos390.WholePaper.upperEndpoint
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@instFintypeOption.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p)
                                              (@Finset.Subtype.fintype.{0} Nat P))
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              Bsource))
                                          (Erdos390.WholePaper.upperTailLength c
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                              (@instFintypeOption.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p)
                                                (@Finset.Subtype.fintype.{0} Nat P))
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                Bsource))))
                                        R)
                                      (@Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                          (@instFintypeOption.{0}
                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p)
                                            (@Finset.Subtype.fintype.{0} Nat P))
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (instDecidableEqFin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Bsource))
                                        (Erdos390.WholePaper.upperEndpoint
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@instFintypeOption.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p)
                                              (@Finset.Subtype.fintype.{0} Nat P))
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              Bsource))
                                          (Erdos390.WholePaper.upperTailLength c
                                            (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                              (@instFintypeOption.{0}
                                                (@Subtype.{1} Nat fun (p : Nat) =>
                                                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                      (@Finset.instSetLike.{0} Nat))
                                                    P p)
                                                (@Finset.Subtype.fintype.{0} Nat P))
                                              (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                                (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                Bsource))))
                                        R depth)
                                      certificate R
                                      (@Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                          (@instFintypeOption.{0}
                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p)
                                            (@Finset.Subtype.fintype.{0} Nat P))
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (instDecidableEqFin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Bsource))
                                        (Erdos390.WholePaper.upperTailLength c
                                          (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@instFintypeOption.{0}
                                              (@Subtype.{1} Nat fun (p : Nat) =>
                                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                    (@Finset.instSetLike.{0} Nat))
                                                  P p)
                                              (@Finset.Subtype.fintype.{0} Nat P))
                                            (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                              (Erdos390.Full.PaperHeadSimplex.Tag P)
                                              (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              Bsource)))
                                        R deltaStar)).factorization
                                  (@Subtype.val.{1} Nat
                                    (fun (p : Nat) =>
                                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                          (@Finset.instSetLike.{0} Nat))
                                        P p)
                                    p)))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@Nat.cast.{0} Real Real.instNatCast
                                  (@Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.exponent P Rhead))
                                qn))) →
                      @Eq.{1} Real qn
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) q0
                            (@Int.cast.{0} Real Real.instIntCast d)) →
                        And
                            (@LE.le.{0} Real Real.instLE
                              (Real.log
                                (Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
                                  Erdos390.Full.PaperBridgeFit.PhysicalSign.minus))
                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) A0
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@Int.cast.{0} Real Real.instIntCast d)
                                      (Erdos390.Full.Scale.L
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                          (@instFintypeOption.{0}
                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p)
                                            (@Finset.Subtype.fintype.{0} Nat P))
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (instDecidableEqFin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Bsource)))))
                                  qn)
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalEta
                                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))
                            (@LE.le.{0} Real Real.instLE
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) A0
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@Int.cast.{0} Real Real.instIntCast d)
                                      (Erdos390.Full.Scale.L
                                        (@Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
                                          (Erdos390.Full.PaperHeadSimplex.Tag P)
                                          (@instFintypeOption.{0}
                                            (@Subtype.{1} Nat fun (p : Nat) =>
                                              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                                  (@Finset.instSetLike.{0} Nat))
                                                P p)
                                            (@Finset.Subtype.fintype.{0} Nat P))
                                          (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (instDecidableEqFin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Bsource)))))
                                  qn)
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalEta
                                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                              (Real.log
                                (Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
                                  Erdos390.Full.PaperBridgeFit.PhysicalSign.plus))) →
                          @Eq.{1} Real
                              (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightRoundedQ0.{0}
                                P (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                                (Fin.fintype
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (instDecidableEqFin
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) K0
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                Bsource c depth R certificate deltaStar betaProt
                                (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0,
                                      0}
                                  (Erdos390.Full.PaperHeadSimplex.Tag P)
                                  (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                  (Fin.fintype
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (instDecidableEqFin
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  Bsource c K0 betaProt betaAct)
                                qTilde)
                              q0 →
                            @Eq.{1} Real
                                (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightA0.{0}
                                  P (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                                  (Fin.fintype
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (instDecidableEqFin
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) K0
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  Bsource c depth R certificate Tsource deltaStar betaProt
                                  (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0,
                                        0}
                                    (Erdos390.Full.PaperHeadSimplex.Tag P)
                                    (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                    (Fin.fintype
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (instDecidableEqFin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    Bsource c K0 betaProt betaAct)
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) betaProt
                                    betaAct)
                                  qTilde)
                                A0 →
                              @Exists.{1}
                                (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
                                  delta eta M P Bsource c depth K0 R certificate
                                  Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals deltaStar
                                  hdelta)
                                fun
                                  (J :
                                    @Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
                                      delta eta M P Bsource c depth K0 R certificate
                                      Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                      deltaStar hdelta) =>
                                And
                                  (@Eq.{1}
                                    (@Erdos390.Full.PaperGuardCensus.BarycentricTarget.{0}
                                      (Erdos390.Full.PaperHeadSimplex.Tag P)
                                      (@instFintypeOption.{0}
                                        (@Subtype.{1} Nat fun (p : Nat) =>
                                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                              (@Finset.instSetLike.{0} Nat))
                                            P p)
                                        (@Finset.Subtype.fintype.{0} Nat P))
                                      (@Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0}
                                        (Erdos390.Full.PaperHeadSimplex.Tag P)
                                        (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
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
                                        (Fin.fintype
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (instDecidableEqFin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        Bsource))
                                    (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.Tsource
                                      delta eta M P Bsource c depth K0 R certificate
                                      Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                      deltaStar hdelta J)
                                    (@Erdos390.Full.PaperBridgeFit.BridgeData.barycentricTargetOfPaperData.{0} P
                                      (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta M)
                                      (Fin.fintype
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      (instDecidableEqFin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge
                                        delta eta M P Bsource c depth K0 R certificate
                                        Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                        deltaStar hdelta J)
                                      Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightHlo
                                        delta eta M P Bsource c depth K0 R certificate
                                        Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                        deltaStar hdelta J)
                                      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightHhi
                                        delta eta M P Bsource c depth K0 R certificate
                                        Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                        deltaStar hdelta J)
                                      Rhead Kphysical))
                                  (And
                                    (@Eq.{1} Real
                                      (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde
                                        delta eta M P Bsource c depth K0 R certificate
                                        Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                        deltaStar hdelta J)
                                      (@Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.activeMass P Rhead))
                                    (And
                                      (@Eq.{1} Nat
                                        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.exponent
                                          delta eta M P Bsource c depth K0 R certificate
                                          Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                          deltaStar hdelta J)
                                        (@Erdos390.Full.PaperGuardCensus.HeadSimplexReserve.exponent P Rhead))
                                      (And
                                        (@Eq.{1} Int
                                          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.d
                                            delta eta M P Bsource c depth K0 R certificate
                                            Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                            deltaStar hdelta J)
                                          d)
                                        (And
                                          (@Eq.{1} Real
                                            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
                                              delta eta M P Bsource c depth K0 R certificate
                                              Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                              deltaStar hdelta J)
                                            betaProt)
                                          (And
                                            (@Eq.{1} Real
                                              (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct
                                                delta eta M P Bsource c depth K0 R certificate
                                                Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                deltaStar hdelta J)
                                              betaAct)
                                            (And
                                              (@Eq.{1} Real
                                                (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.q0
                                                  delta eta M P Bsource c depth K0 R certificate
                                                  Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                  deltaStar hdelta J)
                                                q0)
                                              (And
                                                (@Eq.{1} Real
                                                  (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.A0
                                                    delta eta M P Bsource c depth K0 R certificate
                                                    Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                    deltaStar hdelta J)
                                                  A0)
                                                (And
                                                  (@Eq.{1} Real
                                                    (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qn
                                                      delta eta M P Bsource c depth K0 R certificate
                                                      Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                      deltaStar hdelta J)
                                                    qn)
                                                  (And
                                                    (@Eq.{1} Real
                                                      (@Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs.headMargin.{0}
                                                        P
                                                        (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta
                                                          M)
                                                        (Fin.fintype
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1)))))
                                                        (instDecidableEqFin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1)))))
                                                        Bsource
                                                        Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                        (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightRoundedQ0.{0}
                                                          P
                                                          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta
                                                            M)
                                                          (Fin.fintype
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          (instDecidableEqFin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) K0
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))
                                                          Bsource c depth R certificate deltaStar
                                                          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
                                                            delta eta M P Bsource c depth K0 R certificate
                                                            Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                            deltaStar hdelta J)
                                                          (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0,
                                                                0}
                                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta
                                                              eta M)
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
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P p) =>
                                                                  @Subtype.instDecidableEq.{1} Nat
                                                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P)
                                                                    instDecidableEqNat a b)
                                                                a b)
                                                            (Fin.fintype
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            (instDecidableEqFin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            Bsource c K0
                                                            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
                                                              delta eta M P Bsource c depth K0 R certificate
                                                              Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                              deltaStar hdelta J)
                                                            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct
                                                              delta eta M P Bsource c depth K0 R certificate
                                                              Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                              deltaStar hdelta J))
                                                          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde
                                                            delta eta M P Bsource c depth K0 R certificate
                                                            Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                            deltaStar hdelta J))
                                                        (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightA0.{0}
                                                          P
                                                          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta
                                                            M)
                                                          (Fin.fintype
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          (instDecidableEqFin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) K0
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))
                                                          Bsource c depth R certificate
                                                          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.Tsource
                                                            delta eta M P Bsource c depth K0 R certificate
                                                            Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                            deltaStar hdelta J)
                                                          deltaStar
                                                          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
                                                            delta eta M P Bsource c depth K0 R certificate
                                                            Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                            deltaStar hdelta J)
                                                          (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0,
                                                                0}
                                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta
                                                              eta M)
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
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P p) =>
                                                                  @Subtype.instDecidableEq.{1} Nat
                                                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P)
                                                                    instDecidableEqNat a b)
                                                                a b)
                                                            (Fin.fintype
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            (instDecidableEqFin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            Bsource c K0
                                                            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
                                                              delta eta M P Bsource c depth K0 R certificate
                                                              Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                              deltaStar hdelta J)
                                                            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct
                                                              delta eta M P Bsource c depth K0 R certificate
                                                              Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                              deltaStar hdelta J))
                                                          (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                            (@instHAdd.{0} Real Real.instAdd)
                                                            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
                                                              delta eta M P Bsource c depth K0 R certificate
                                                              Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                              deltaStar hdelta J)
                                                            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct
                                                              delta eta M P Bsource c depth K0 R certificate
                                                              Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                              deltaStar hdelta J))
                                                          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde
                                                            delta eta M P Bsource c depth K0 R certificate
                                                            Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                            deltaStar hdelta J))
                                                        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.d
                                                          delta eta M P Bsource c depth K0 R certificate
                                                          Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                          deltaStar hdelta J)
                                                        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.exponent
                                                          delta eta M P Bsource c depth K0 R certificate
                                                          Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                          deltaStar hdelta J)
                                                        (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightActiveHeadTarget.{0}
                                                          P
                                                          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta
                                                            M)
                                                          (Fin.fintype
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          (instDecidableEqFin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          Bsource c depth R certificate deltaStar)
                                                        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.targetInputs
                                                          delta eta M P Bsource c depth K0 R certificate
                                                          Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                          deltaStar hdelta J))
                                                      postMargin)
                                                    (@Eq.{1} Real
                                                      (@Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs.physicalEta.{0}
                                                        P
                                                        (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta
                                                          M)
                                                        (Fin.fintype
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1)))))
                                                        (instDecidableEqFin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1)))))
                                                        Bsource
                                                        Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                        (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightRoundedQ0.{0}
                                                          P
                                                          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta
                                                            M)
                                                          (Fin.fintype
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          (instDecidableEqFin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) K0
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))
                                                          Bsource c depth R certificate deltaStar
                                                          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
                                                            delta eta M P Bsource c depth K0 R certificate
                                                            Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                            deltaStar hdelta J)
                                                          (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0,
                                                                0}
                                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta
                                                              eta M)
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
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P p) =>
                                                                  @Subtype.instDecidableEq.{1} Nat
                                                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P)
                                                                    instDecidableEqNat a b)
                                                                a b)
                                                            (Fin.fintype
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            (instDecidableEqFin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            Bsource c K0
                                                            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
                                                              delta eta M P Bsource c depth K0 R certificate
                                                              Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                              deltaStar hdelta J)
                                                            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct
                                                              delta eta M P Bsource c depth K0 R certificate
                                                              Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                              deltaStar hdelta J))
                                                          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde
                                                            delta eta M P Bsource c depth K0 R certificate
                                                            Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                            deltaStar hdelta J))
                                                        (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightA0.{0}
                                                          P
                                                          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta
                                                            M)
                                                          (Fin.fintype
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          (instDecidableEqFin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) K0
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))
                                                          Bsource c depth R certificate
                                                          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.Tsource
                                                            delta eta M P Bsource c depth K0 R certificate
                                                            Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                            deltaStar hdelta J)
                                                          deltaStar
                                                          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
                                                            delta eta M P Bsource c depth K0 R certificate
                                                            Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                            deltaStar hdelta J)
                                                          (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha.{0,
                                                                0}
                                                            (Erdos390.Full.PaperHeadSimplex.Tag P)
                                                            (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta
                                                              eta M)
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
                                                                          (@SetLike.instMembership.{0, 0}
                                                                            (Finset.{0} Nat) Nat
                                                                            (@Finset.instSetLike.{0} Nat))
                                                                          P p) =>
                                                                  @Subtype.instDecidableEq.{1} Nat
                                                                    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                                                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat)
                                                                        Nat (@Finset.instSetLike.{0} Nat))
                                                                      P)
                                                                    instDecidableEqNat a b)
                                                                a b)
                                                            (Fin.fintype
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            (instDecidableEqFin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1)))))
                                                            Bsource c K0
                                                            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
                                                              delta eta M P Bsource c depth K0 R certificate
                                                              Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                              deltaStar hdelta J)
                                                            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct
                                                              delta eta M P Bsource c depth K0 R certificate
                                                              Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                              deltaStar hdelta J))
                                                          (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                            (@instHAdd.{0} Real Real.instAdd)
                                                            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaProt
                                                              delta eta M P Bsource c depth K0 R certificate
                                                              Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                              deltaStar hdelta J)
                                                            (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.betaAct
                                                              delta eta M P Bsource c depth K0 R certificate
                                                              Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                              deltaStar hdelta J))
                                                          (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qTilde
                                                            delta eta M P Bsource c depth K0 R certificate
                                                            Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                            deltaStar hdelta J))
                                                        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.d
                                                          delta eta M P Bsource c depth K0 R certificate
                                                          Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                          deltaStar hdelta J)
                                                        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.exponent
                                                          delta eta M P Bsource c depth K0 R certificate
                                                          Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                          deltaStar hdelta J)
                                                        (@Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeightActiveHeadTarget.{0}
                                                          P
                                                          (@Erdos390.WholePaper.BankPaperCanonicalExponentBand delta eta
                                                            M)
                                                          (Fin.fintype
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          (instDecidableEqFin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          Bsource c depth R certificate deltaStar)
                                                        (@Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.targetInputs
                                                          delta eta M P Bsource c depth K0 R certificate
                                                          Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                                          deltaStar hdelta J))
                                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                        (@instHDiv.{0} Real
                                                          (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                        Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeightPhysicalEta
                                                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                                                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                                            (@Nat.instAtLeastTwoHAddOfNat
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))
                                                              (@Nat.instNeZeroSucc
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                  (instOfNatNat (nat_lit 0)))))))))))))))))) := by sorry
