-- Prove2me | Definitions.Def_erdos390_analytic_compact_goals_006
-- name    : erdos390_analytic_compact_goals_006
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T17:18:28.189089+00:00
-- url     : https://prove2.me/theorems/e94c8158-bee8-4f12-86c9-3f70eee7effa
-- title:
--   Fine-mesh ordinary projected inverse proposition
-- statement:
--   This file names the fully quantified fine-mesh ordinary projected raw inverse proposition, including its eventual cutoff, mesh, anchor, and arithmetic hypotheses. The proposition is definitionally identical to the source statement and asserts no new mathematical fact or axiom.
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

set_option maxRecDepth 10000
set_option maxHeartbeats 0

noncomputable def Erdos390.AnalyticCompactBatch006Goal001 : Prop :=
@Exists.{1} Real fun (Cref : Real) =>
  And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Cref)
    (@Exists.{1} Real fun (meshTol : Real) =>
      And
        (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          meshTol)
        (@Exists.{1} Nat fun (W₀ : Nat) =>
          ∀ (W : Nat),
            @LE.le.{0} Nat instLENat W₀ W →
              ∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta)
                (hdelta :
                  @LT.lt.{0} Real Real.instLT
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta),
                @LE.le.{0} Real Real.instLE
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) delta
                      (@Erdos390.Full.RegularRelativeMesh.Mesh.ratio delta eta M))
                    meshTol →
                  @Filter.Eventually.{0} Nat
                    (fun (n : Nat) =>
                      @Exists.{0} (@Ne.{1} Nat W (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        fun (hWne : @Ne.{1} Nat W (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) =>
                        @Exists.{0}
                          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
                          fun
                            (hn :
                              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                n) =>
                          @Exists.{0} (@Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation delta eta M n W)
                            fun (S : @Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation delta eta M n W) =>
                            let P :=
                              @Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition delta eta M n W hdelta hn
                                hWne S;
                            let E :=
                              @Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalCertificate delta eta M n W hdelta hn
                                hWne S;
                            ∀
                              (q :
                                @Subtype.{1}
                                  (Fin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                    Real)
                                  fun
                                    (x :
                                      Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                        Real) =>
                                  @Membership.mem.{0, 0}
                                    (Fin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                      Real)
                                    (@Submodule.{0, 0} Real
                                      (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                        Real)
                                      Real.semiring
                                      (@Pi.addCommMonoid.{0, 0}
                                        (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (fun
                                            (a :
                                              Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                          Real)
                                        fun
                                          (i :
                                            Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                        Real.instAddCommMonoid)
                                      (@Pi.Function.module.{0, 0, 0}
                                        (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        Real Real Real.semiring Real.instAddCommMonoid
                                        (@Semiring.toModule.{0} Real Real.semiring)))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Submodule.{0, 0} Real
                                        (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                          Real)
                                        Real.semiring
                                        (@Pi.addCommMonoid.{0, 0}
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (fun
                                              (a :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                            Real)
                                          fun
                                            (i :
                                              Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                          Real.instAddCommMonoid)
                                        (@Pi.Function.module.{0, 0, 0}
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          Real Real Real.semiring Real.instAddCommMonoid
                                          (@Semiring.toModule.{0} Real Real.semiring)))
                                      (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                        Real)
                                      (@Submodule.setLike.{0, 0} Real
                                        (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                          Real)
                                        Real.semiring
                                        (@Pi.addCommMonoid.{0, 0}
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (fun
                                              (a :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                            Real)
                                          fun
                                            (i :
                                              Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                          Real.instAddCommMonoid)
                                        (@Pi.Function.module.{0, 0, 0}
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          Real Real Real.semiring Real.instAddCommMonoid
                                          (@Semiring.toModule.{0} Real Real.semiring))))
                                    (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                      (Fin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      (Fin.fintype
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                        (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (Fin.fintype
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (instDecidableEqFin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        P)
                                      (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                        (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (Fin.fintype
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (instDecidableEqFin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        P))
                                    x),
                              @LE.le.{0} Real Real.instLE
                                (@Norm.norm.{0}
                                  (@Subtype.{1}
                                    (Fin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                      Real)
                                    fun
                                      (x :
                                        Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                          Real) =>
                                    @Membership.mem.{0, 0}
                                      (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                        Real)
                                      (@Submodule.{0, 0} Real
                                        (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                          Real)
                                        Real.semiring
                                        (@Pi.addCommMonoid.{0, 0}
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (fun
                                              (a :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                            Real)
                                          fun
                                            (i :
                                              Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                          Real.instAddCommMonoid)
                                        (@Pi.Function.module.{0, 0, 0}
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          Real Real Real.semiring Real.instAddCommMonoid
                                          (@Semiring.toModule.{0} Real Real.semiring)))
                                      (@SetLike.instMembership.{0, 0}
                                        (@Submodule.{0, 0} Real
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          Real.semiring
                                          (@Pi.addCommMonoid.{0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (fun
                                                (a :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real)
                                            fun
                                              (i :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                            Real.instAddCommMonoid)
                                          (@Pi.Function.module.{0, 0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Real Real Real.semiring Real.instAddCommMonoid
                                            (@Semiring.toModule.{0} Real Real.semiring)))
                                        (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                          Real)
                                        (@Submodule.setLike.{0, 0} Real
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          Real.semiring
                                          (@Pi.addCommMonoid.{0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (fun
                                                (a :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real)
                                            fun
                                              (i :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                            Real.instAddCommMonoid)
                                          (@Pi.Function.module.{0, 0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Real Real Real.semiring Real.instAddCommMonoid
                                            (@Semiring.toModule.{0} Real Real.semiring))))
                                      (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                        (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (Fin.fintype
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (Fin.fintype
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (instDecidableEqFin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          P)
                                        (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (Fin.fintype
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (instDecidableEqFin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          P))
                                      x)
                                  (@NormedAddCommGroup.toNorm.{0}
                                    (@Subtype.{1}
                                      (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                        Real)
                                      fun
                                        (x :
                                          Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real) =>
                                      @Membership.mem.{0, 0}
                                        (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                          Real)
                                        (@Submodule.{0, 0} Real
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          Real.semiring
                                          (@Pi.addCommMonoid.{0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (fun
                                                (a :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real)
                                            fun
                                              (i :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                            Real.instAddCommMonoid)
                                          (@Pi.Function.module.{0, 0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Real Real Real.semiring Real.instAddCommMonoid
                                            (@Semiring.toModule.{0} Real Real.semiring)))
                                        (@SetLike.instMembership.{0, 0}
                                          (@Submodule.{0, 0} Real
                                            (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              Real)
                                            Real.semiring
                                            (@Pi.addCommMonoid.{0, 0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (fun
                                                  (a :
                                                    Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) =>
                                                Real)
                                              fun
                                                (i :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real.instAddCommMonoid)
                                            (@Pi.Function.module.{0, 0, 0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              Real Real Real.semiring Real.instAddCommMonoid
                                              (@Semiring.toModule.{0} Real Real.semiring)))
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          (@Submodule.setLike.{0, 0} Real
                                            (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              Real)
                                            Real.semiring
                                            (@Pi.addCommMonoid.{0, 0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (fun
                                                  (a :
                                                    Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) =>
                                                Real)
                                              fun
                                                (i :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real.instAddCommMonoid)
                                            (@Pi.Function.module.{0, 0, 0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              Real Real Real.semiring Real.instAddCommMonoid
                                              (@Semiring.toModule.{0} Real Real.semiring))))
                                        (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (Fin.fintype
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (instDecidableEqFin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            P)
                                          (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (instDecidableEqFin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            P))
                                        x)
                                    (@Submodule.normedAddCommGroup.{0, 0} Real
                                      (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                        Real)
                                      Real.instRing
                                      (@Pi.normedAddCommGroup.{0, 0}
                                        (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (fun
                                            (a :
                                              Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                          Real)
                                        (Fin.fintype
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        fun
                                          (i :
                                            Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                        Real.normedAddCommGroup)
                                      (@Pi.Function.module.{0, 0, 0}
                                        (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        Real Real Real.semiring Real.instAddCommMonoid
                                        (@Semiring.toModule.{0} Real Real.semiring))
                                      (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                        (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (Fin.fintype
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (Fin.fintype
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (instDecidableEqFin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          P)
                                        (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (Fin.fintype
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (instDecidableEqFin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          P))))
                                  q)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Cref
                                  (@Norm.norm.{0}
                                    (@Subtype.{1}
                                      (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                        Real)
                                      fun
                                        (x :
                                          Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real) =>
                                      @Membership.mem.{0, 0}
                                        (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                          Real)
                                        (@Submodule.{0, 0} Real
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          Real.semiring
                                          (@Pi.addCommMonoid.{0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (fun
                                                (a :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real)
                                            fun
                                              (i :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                            Real.instAddCommMonoid)
                                          (@Pi.Function.module.{0, 0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Real Real Real.semiring Real.instAddCommMonoid
                                            (@Semiring.toModule.{0} Real Real.semiring)))
                                        (@SetLike.instMembership.{0, 0}
                                          (@Submodule.{0, 0} Real
                                            (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              Real)
                                            Real.semiring
                                            (@Pi.addCommMonoid.{0, 0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (fun
                                                  (a :
                                                    Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) =>
                                                Real)
                                              fun
                                                (i :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real.instAddCommMonoid)
                                            (@Pi.Function.module.{0, 0, 0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              Real Real Real.semiring Real.instAddCommMonoid
                                              (@Semiring.toModule.{0} Real Real.semiring)))
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          (@Submodule.setLike.{0, 0} Real
                                            (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              Real)
                                            Real.semiring
                                            (@Pi.addCommMonoid.{0, 0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (fun
                                                  (a :
                                                    Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) =>
                                                Real)
                                              fun
                                                (i :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real.instAddCommMonoid)
                                            (@Pi.Function.module.{0, 0, 0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              Real Real Real.semiring Real.instAddCommMonoid
                                              (@Semiring.toModule.{0} Real Real.semiring))))
                                        (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (Fin.fintype
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (instDecidableEqFin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            P)
                                          (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (instDecidableEqFin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            P))
                                        x)
                                    (@NormedAddCommGroup.toNorm.{0}
                                      (@Subtype.{1}
                                        (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                          Real)
                                        fun
                                          (x :
                                            Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              Real) =>
                                        @Membership.mem.{0, 0}
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          (@Submodule.{0, 0} Real
                                            (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              Real)
                                            Real.semiring
                                            (@Pi.addCommMonoid.{0, 0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (fun
                                                  (a :
                                                    Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) =>
                                                Real)
                                              fun
                                                (i :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real.instAddCommMonoid)
                                            (@Pi.Function.module.{0, 0, 0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              Real Real Real.semiring Real.instAddCommMonoid
                                              (@Semiring.toModule.{0} Real Real.semiring)))
                                          (@SetLike.instMembership.{0, 0}
                                            (@Submodule.{0, 0} Real
                                              (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real)
                                              Real.semiring
                                              (@Pi.addCommMonoid.{0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (fun
                                                    (a :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real)
                                                fun
                                                  (i :
                                                    Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) =>
                                                Real.instAddCommMonoid)
                                              (@Pi.Function.module.{0, 0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                Real Real Real.semiring Real.instAddCommMonoid
                                                (@Semiring.toModule.{0} Real Real.semiring)))
                                            (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              Real)
                                            (@Submodule.setLike.{0, 0} Real
                                              (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real)
                                              Real.semiring
                                              (@Pi.addCommMonoid.{0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (fun
                                                    (a :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real)
                                                fun
                                                  (i :
                                                    Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) =>
                                                Real.instAddCommMonoid)
                                              (@Pi.Function.module.{0, 0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                Real Real Real.semiring Real.instAddCommMonoid
                                                (@Semiring.toModule.{0} Real Real.semiring))))
                                          (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P))
                                          x)
                                      (@Submodule.normedAddCommGroup.{0, 0} Real
                                        (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                          Real)
                                        Real.instRing
                                        (@Pi.normedAddCommGroup.{0, 0}
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (fun
                                              (a :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                            Real)
                                          (Fin.fintype
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          fun
                                            (i :
                                              Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                          Real.normedAddCommGroup)
                                        (@Pi.Function.module.{0, 0, 0}
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          Real Real Real.semiring Real.instAddCommMonoid
                                          (@Semiring.toModule.{0} Real Real.semiring))
                                        (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (Fin.fintype
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (instDecidableEqFin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            P)
                                          (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (instDecidableEqFin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            P))))
                                    (@DFunLike.coe.{1, 1, 1}
                                      (@LinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                                        (@Subtype.{1}
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          fun
                                            (x :
                                              Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real) =>
                                          @Membership.mem.{0, 0}
                                            (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              Real)
                                            (@Submodule.{0, 0} Real
                                              (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real)
                                              Real.semiring
                                              (@Pi.addCommMonoid.{0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (fun
                                                    (a :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real)
                                                fun
                                                  (i :
                                                    Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) =>
                                                Real.instAddCommMonoid)
                                              (@Pi.Function.module.{0, 0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                Real Real Real.semiring Real.instAddCommMonoid
                                                (@Semiring.toModule.{0} Real Real.semiring)))
                                            (@SetLike.instMembership.{0, 0}
                                              (@Submodule.{0, 0} Real
                                                (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                  Real)
                                                Real.semiring
                                                (@Pi.addCommMonoid.{0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (fun
                                                      (a :
                                                        Fin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))) =>
                                                    Real)
                                                  fun
                                                    (i :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real.instAddCommMonoid)
                                                (@Pi.Function.module.{0, 0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  Real Real Real.semiring Real.instAddCommMonoid
                                                  (@Semiring.toModule.{0} Real Real.semiring)))
                                              (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real)
                                              (@Submodule.setLike.{0, 0} Real
                                                (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                  Real)
                                                Real.semiring
                                                (@Pi.addCommMonoid.{0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (fun
                                                      (a :
                                                        Fin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))) =>
                                                    Real)
                                                  fun
                                                    (i :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real.instAddCommMonoid)
                                                (@Pi.Function.module.{0, 0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  Real Real Real.semiring Real.instAddCommMonoid
                                                  (@Semiring.toModule.{0} Real Real.semiring))))
                                            (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                P)
                                              (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                P))
                                            x)
                                        (@Subtype.{1}
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          fun
                                            (x :
                                              Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real) =>
                                          @Membership.mem.{0, 0}
                                            (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              Real)
                                            (@Submodule.{0, 0} Real
                                              (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real)
                                              Real.semiring
                                              (@Pi.addCommMonoid.{0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (fun
                                                    (a :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real)
                                                fun
                                                  (i :
                                                    Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) =>
                                                Real.instAddCommMonoid)
                                              (@Pi.Function.module.{0, 0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                Real Real Real.semiring Real.instAddCommMonoid
                                                (@Semiring.toModule.{0} Real Real.semiring)))
                                            (@SetLike.instMembership.{0, 0}
                                              (@Submodule.{0, 0} Real
                                                (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                  Real)
                                                Real.semiring
                                                (@Pi.addCommMonoid.{0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (fun
                                                      (a :
                                                        Fin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))) =>
                                                    Real)
                                                  fun
                                                    (i :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real.instAddCommMonoid)
                                                (@Pi.Function.module.{0, 0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  Real Real Real.semiring Real.instAddCommMonoid
                                                  (@Semiring.toModule.{0} Real Real.semiring)))
                                              (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real)
                                              (@Submodule.setLike.{0, 0} Real
                                                (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                  Real)
                                                Real.semiring
                                                (@Pi.addCommMonoid.{0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (fun
                                                      (a :
                                                        Fin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))) =>
                                                    Real)
                                                  fun
                                                    (i :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real.instAddCommMonoid)
                                                (@Pi.Function.module.{0, 0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  Real Real Real.semiring Real.instAddCommMonoid
                                                  (@Semiring.toModule.{0} Real Real.semiring))))
                                            (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                P)
                                              (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                P))
                                            x)
                                        (@Submodule.addCommMonoid.{0, 0} Real
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          Real.semiring
                                          (@Pi.addCommMonoid.{0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (fun
                                                (a :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real)
                                            fun
                                              (i :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                            Real.instAddCommMonoid)
                                          (@Pi.Function.module.{0, 0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Real Real Real.semiring Real.instAddCommMonoid
                                            (@Semiring.toModule.{0} Real Real.semiring))
                                          (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)))
                                        (@Submodule.addCommMonoid.{0, 0} Real
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          Real.semiring
                                          (@Pi.addCommMonoid.{0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (fun
                                                (a :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real)
                                            fun
                                              (i :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                            Real.instAddCommMonoid)
                                          (@Pi.Function.module.{0, 0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Real Real Real.semiring Real.instAddCommMonoid
                                            (@Semiring.toModule.{0} Real Real.semiring))
                                          (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)))
                                        (@Submodule.module.{0, 0} Real
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          Real.semiring
                                          (@Pi.addCommMonoid.{0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (fun
                                                (a :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real)
                                            fun
                                              (i :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                            Real.instAddCommMonoid)
                                          (@Pi.Function.module.{0, 0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Real Real Real.semiring Real.instAddCommMonoid
                                            (@Semiring.toModule.{0} Real Real.semiring))
                                          (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)))
                                        (@Submodule.module.{0, 0} Real
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          Real.semiring
                                          (@Pi.addCommMonoid.{0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (fun
                                                (a :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real)
                                            fun
                                              (i :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                            Real.instAddCommMonoid)
                                          (@Pi.Function.module.{0, 0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Real Real Real.semiring Real.instAddCommMonoid
                                            (@Semiring.toModule.{0} Real Real.semiring))
                                          (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P))))
                                      (@Subtype.{1}
                                        (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                          Real)
                                        fun
                                          (x :
                                            Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              Real) =>
                                        @Membership.mem.{0, 0}
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          (@Submodule.{0, 0} Real
                                            (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              Real)
                                            Real.semiring
                                            (@Pi.addCommMonoid.{0, 0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (fun
                                                  (a :
                                                    Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) =>
                                                Real)
                                              fun
                                                (i :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real.instAddCommMonoid)
                                            (@Pi.Function.module.{0, 0, 0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              Real Real Real.semiring Real.instAddCommMonoid
                                              (@Semiring.toModule.{0} Real Real.semiring)))
                                          (@SetLike.instMembership.{0, 0}
                                            (@Submodule.{0, 0} Real
                                              (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real)
                                              Real.semiring
                                              (@Pi.addCommMonoid.{0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (fun
                                                    (a :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real)
                                                fun
                                                  (i :
                                                    Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) =>
                                                Real.instAddCommMonoid)
                                              (@Pi.Function.module.{0, 0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                Real Real Real.semiring Real.instAddCommMonoid
                                                (@Semiring.toModule.{0} Real Real.semiring)))
                                            (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              Real)
                                            (@Submodule.setLike.{0, 0} Real
                                              (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real)
                                              Real.semiring
                                              (@Pi.addCommMonoid.{0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (fun
                                                    (a :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real)
                                                fun
                                                  (i :
                                                    Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) =>
                                                Real.instAddCommMonoid)
                                              (@Pi.Function.module.{0, 0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                Real Real Real.semiring Real.instAddCommMonoid
                                                (@Semiring.toModule.{0} Real Real.semiring))))
                                          (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P))
                                          x)
                                      (fun
                                          (x :
                                            @Subtype.{1}
                                              (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real)
                                              fun
                                                (x :
                                                  Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                    Real) =>
                                              @Membership.mem.{0, 0}
                                                (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                  Real)
                                                (@Submodule.{0, 0} Real
                                                  (Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                    Real)
                                                  Real.semiring
                                                  (@Pi.addCommMonoid.{0, 0}
                                                    (Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (fun
                                                        (a :
                                                          Fin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1))))) =>
                                                      Real)
                                                    fun
                                                      (i :
                                                        Fin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))) =>
                                                    Real.instAddCommMonoid)
                                                  (@Pi.Function.module.{0, 0, 0}
                                                    (Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    Real Real Real.semiring Real.instAddCommMonoid
                                                    (@Semiring.toModule.{0} Real Real.semiring)))
                                                (@SetLike.instMembership.{0, 0}
                                                  (@Submodule.{0, 0} Real
                                                    (Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))) →
                                                      Real)
                                                    Real.semiring
                                                    (@Pi.addCommMonoid.{0, 0}
                                                      (Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      (fun
                                                          (a :
                                                            Fin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1))))) =>
                                                        Real)
                                                      fun
                                                        (i :
                                                          Fin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1))))) =>
                                                      Real.instAddCommMonoid)
                                                    (@Pi.Function.module.{0, 0, 0}
                                                      (Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      Real Real Real.semiring Real.instAddCommMonoid
                                                      (@Semiring.toModule.{0} Real Real.semiring)))
                                                  (Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                    Real)
                                                  (@Submodule.setLike.{0, 0} Real
                                                    (Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))) →
                                                      Real)
                                                    Real.semiring
                                                    (@Pi.addCommMonoid.{0, 0}
                                                      (Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      (fun
                                                          (a :
                                                            Fin
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                  eta M)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1))))) =>
                                                        Real)
                                                      fun
                                                        (i :
                                                          Fin
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta
                                                                eta M)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1))))) =>
                                                      Real.instAddCommMonoid)
                                                    (@Pi.Function.module.{0, 0, 0}
                                                      (Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      Real Real Real.semiring Real.instAddCommMonoid
                                                      (@Semiring.toModule.{0} Real Real.semiring))))
                                                (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (Fin.fintype
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                                    (Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (Fin.fintype
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (instDecidableEqFin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    P)
                                                  (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                                    (Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (Fin.fintype
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (instDecidableEqFin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    P))
                                                x) =>
                                        @Subtype.{1}
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          fun
                                            (x :
                                              Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real) =>
                                          @Membership.mem.{0, 0}
                                            (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              Real)
                                            (@Submodule.{0, 0} Real
                                              (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real)
                                              Real.semiring
                                              (@Pi.addCommMonoid.{0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (fun
                                                    (a :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real)
                                                fun
                                                  (i :
                                                    Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) =>
                                                Real.instAddCommMonoid)
                                              (@Pi.Function.module.{0, 0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                Real Real Real.semiring Real.instAddCommMonoid
                                                (@Semiring.toModule.{0} Real Real.semiring)))
                                            (@SetLike.instMembership.{0, 0}
                                              (@Submodule.{0, 0} Real
                                                (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                  Real)
                                                Real.semiring
                                                (@Pi.addCommMonoid.{0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (fun
                                                      (a :
                                                        Fin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))) =>
                                                    Real)
                                                  fun
                                                    (i :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real.instAddCommMonoid)
                                                (@Pi.Function.module.{0, 0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  Real Real Real.semiring Real.instAddCommMonoid
                                                  (@Semiring.toModule.{0} Real Real.semiring)))
                                              (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real)
                                              (@Submodule.setLike.{0, 0} Real
                                                (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                  Real)
                                                Real.semiring
                                                (@Pi.addCommMonoid.{0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (fun
                                                      (a :
                                                        Fin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))) =>
                                                    Real)
                                                  fun
                                                    (i :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real.instAddCommMonoid)
                                                (@Pi.Function.module.{0, 0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  Real Real Real.semiring Real.instAddCommMonoid
                                                  (@Semiring.toModule.{0} Real Real.semiring))))
                                            (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                P)
                                              (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                P))
                                            x)
                                      (@LinearMap.instFunLike.{0, 0, 0, 0} Real Real
                                        (@Subtype.{1}
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          fun
                                            (x :
                                              Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real) =>
                                          @Membership.mem.{0, 0}
                                            (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              Real)
                                            (@Submodule.{0, 0} Real
                                              (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real)
                                              Real.semiring
                                              (@Pi.addCommMonoid.{0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (fun
                                                    (a :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real)
                                                fun
                                                  (i :
                                                    Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) =>
                                                Real.instAddCommMonoid)
                                              (@Pi.Function.module.{0, 0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                Real Real Real.semiring Real.instAddCommMonoid
                                                (@Semiring.toModule.{0} Real Real.semiring)))
                                            (@SetLike.instMembership.{0, 0}
                                              (@Submodule.{0, 0} Real
                                                (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                  Real)
                                                Real.semiring
                                                (@Pi.addCommMonoid.{0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (fun
                                                      (a :
                                                        Fin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))) =>
                                                    Real)
                                                  fun
                                                    (i :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real.instAddCommMonoid)
                                                (@Pi.Function.module.{0, 0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  Real Real Real.semiring Real.instAddCommMonoid
                                                  (@Semiring.toModule.{0} Real Real.semiring)))
                                              (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real)
                                              (@Submodule.setLike.{0, 0} Real
                                                (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                  Real)
                                                Real.semiring
                                                (@Pi.addCommMonoid.{0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (fun
                                                      (a :
                                                        Fin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))) =>
                                                    Real)
                                                  fun
                                                    (i :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real.instAddCommMonoid)
                                                (@Pi.Function.module.{0, 0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  Real Real Real.semiring Real.instAddCommMonoid
                                                  (@Semiring.toModule.{0} Real Real.semiring))))
                                            (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                P)
                                              (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                P))
                                            x)
                                        (@Subtype.{1}
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          fun
                                            (x :
                                              Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real) =>
                                          @Membership.mem.{0, 0}
                                            (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              Real)
                                            (@Submodule.{0, 0} Real
                                              (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real)
                                              Real.semiring
                                              (@Pi.addCommMonoid.{0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (fun
                                                    (a :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real)
                                                fun
                                                  (i :
                                                    Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) =>
                                                Real.instAddCommMonoid)
                                              (@Pi.Function.module.{0, 0, 0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                Real Real Real.semiring Real.instAddCommMonoid
                                                (@Semiring.toModule.{0} Real Real.semiring)))
                                            (@SetLike.instMembership.{0, 0}
                                              (@Submodule.{0, 0} Real
                                                (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                  Real)
                                                Real.semiring
                                                (@Pi.addCommMonoid.{0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (fun
                                                      (a :
                                                        Fin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))) =>
                                                    Real)
                                                  fun
                                                    (i :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real.instAddCommMonoid)
                                                (@Pi.Function.module.{0, 0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  Real Real Real.semiring Real.instAddCommMonoid
                                                  (@Semiring.toModule.{0} Real Real.semiring)))
                                              (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                Real)
                                              (@Submodule.setLike.{0, 0} Real
                                                (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                                  Real)
                                                Real.semiring
                                                (@Pi.addCommMonoid.{0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (fun
                                                      (a :
                                                        Fin
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                              M)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))) =>
                                                    Real)
                                                  fun
                                                    (i :
                                                      Fin
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta
                                                            M)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) =>
                                                  Real.instAddCommMonoid)
                                                (@Pi.Function.module.{0, 0, 0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  Real Real Real.semiring Real.instAddCommMonoid
                                                  (@Semiring.toModule.{0} Real Real.semiring))))
                                            (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                P)
                                              (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                P))
                                            x)
                                        Real.semiring Real.semiring
                                        (@Submodule.addCommMonoid.{0, 0} Real
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          Real.semiring
                                          (@Pi.addCommMonoid.{0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (fun
                                                (a :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real)
                                            fun
                                              (i :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                            Real.instAddCommMonoid)
                                          (@Pi.Function.module.{0, 0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Real Real Real.semiring Real.instAddCommMonoid
                                            (@Semiring.toModule.{0} Real Real.semiring))
                                          (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)))
                                        (@Submodule.addCommMonoid.{0, 0} Real
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          Real.semiring
                                          (@Pi.addCommMonoid.{0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (fun
                                                (a :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real)
                                            fun
                                              (i :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                            Real.instAddCommMonoid)
                                          (@Pi.Function.module.{0, 0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Real Real Real.semiring Real.instAddCommMonoid
                                            (@Semiring.toModule.{0} Real Real.semiring))
                                          (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)))
                                        (@Submodule.module.{0, 0} Real
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          Real.semiring
                                          (@Pi.addCommMonoid.{0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (fun
                                                (a :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real)
                                            fun
                                              (i :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                            Real.instAddCommMonoid)
                                          (@Pi.Function.module.{0, 0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Real Real Real.semiring Real.instAddCommMonoid
                                            (@Semiring.toModule.{0} Real Real.semiring))
                                          (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)))
                                        (@Submodule.module.{0, 0} Real
                                          (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                            Real)
                                          Real.semiring
                                          (@Pi.addCommMonoid.{0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (fun
                                                (a :
                                                  Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                              Real)
                                            fun
                                              (i :
                                                Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                            Real.instAddCommMonoid)
                                          (@Pi.Function.module.{0, 0, 0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            Real Real Real.semiring Real.instAddCommMonoid
                                            (@Semiring.toModule.{0} Real Real.semiring))
                                          (@Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{0}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)))
                                        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)))
                                      (@Erdos390.Full.PaperWeightedInverseExport.projectedRawLinearMap.{0}
                                        (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (Fin.fintype
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (@Erdos390.Full.CompressedArithmeticOperator.arithmeticDiagonal.{0}
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (Erdos390.Full.ArithmeticModel.y n)
                                          (@Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{0} n W
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (@Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition delta eta M
                                              n W hdelta hn hWne S)
                                            E)
                                          (@Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{0} n W
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (@Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition delta eta M
                                              n W hdelta hn hWne S)
                                            E))
                                        (@Erdos390.Full.CompressedArithmeticOperator.arithmeticKernel.{0}
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (Erdos390.Full.ArithmeticModel.y n)
                                          (@Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{0} n W
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (@Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition delta eta M
                                              n W hdelta hn hWne S)
                                            E)
                                          (@Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{0} n W
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin.fintype
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (@Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition delta eta M
                                              n W hdelta hn hWne S)
                                            E))
                                        (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (Fin.fintype
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (instDecidableEqFin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          P)
                                        (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (Fin.fintype
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (instDecidableEqFin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          P)
                                        (@Eq.mpr.{0}
                                          (@Ne.{1} Real
                                            (@Erdos390.Full.MovingLowGaugeTransfer.sharpWeightTotal.{0}
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                P)
                                              (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                P))
                                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                                          (@Ne.{1} Real
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.centerEnergy.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)
                                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                                          (@id.{0}
                                            (@Eq.{1} Prop
                                              (@Ne.{1} Real
                                                (@Erdos390.Full.MovingLowGaugeTransfer.sharpWeightTotal.{0}
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (Fin.fintype
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                                    (Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (Fin.fintype
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (instDecidableEqFin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    P)
                                                  (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                                    (Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (Fin.fintype
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (instDecidableEqFin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    P))
                                                (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                  (@Zero.toOfNat0.{0} Real Real.instZero)))
                                              (@Ne.{1} Real
                                                (@Erdos390.Full.ArithmeticBandGeometry.Partition.centerEnergy.{0} n W
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (Fin.fintype
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (instDecidableEqFin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  P)
                                                (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                  (@Zero.toOfNat0.{0} Real Real.instZero))))
                                            (@congrArg.{1, 1} Real Prop
                                              (@Erdos390.Full.MovingLowGaugeTransfer.sharpWeightTotal.{0}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (@Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{0} n W
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (Fin.fintype
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (instDecidableEqFin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  P)
                                                (@Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} n W
                                                  (Fin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (Fin.fintype
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (instDecidableEqFin
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  P))
                                              (@Erdos390.Full.ArithmeticBandGeometry.Partition.centerEnergy.{0} n W
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                P)
                                              (fun (_a : Real) =>
                                                @Ne.{1} Real _a
                                                  (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                    (@Zero.toOfNat0.{0} Real Real.instZero)))
                                              (@Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.sharpWeightTotal_partition_eq_centerEnergy.{0}
                                                n W
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (Fin.fintype
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (instDecidableEqFin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                P)))
                                          (@LT.lt.ne'.{0} Real Real.instPreorder
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.centerEnergy.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P)
                                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                            (@Erdos390.Full.ArithmeticBandGeometry.Partition.centerEnergy_pos.{0} n W
                                              (Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (Fin.fintype
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (instDecidableEqFin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              P
                                              (@instNonemptyOfInhabited.{1}
                                                (Fin
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (@Fin.instInhabited
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                  (@instNeZeroNatHAdd_1
                                                    (@Erdos390.Full.RegularRelativeMesh.Mesh.cellCount delta eta M)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                                    (@Nat.instNeZeroSucc
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                              hn))))
                                      q))))
                    (@Filter.atTop.{0} Nat Nat.instPreorder)))


