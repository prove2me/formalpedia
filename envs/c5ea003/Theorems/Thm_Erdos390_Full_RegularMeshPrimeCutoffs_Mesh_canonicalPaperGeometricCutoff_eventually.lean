-- Prove2me | Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalPaperGeometricCutoff_eventually
-- name    : Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricCutoff_eventually
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:52:26.48668+00:00
-- url     : https://prove2.me/theorems/c35ca6aa-466b-49eb-8e47-e0212d008e77
-- title:
--   Canonical geometric bounds at the paper mesh scale
-- statement:
--   For cMesh>0, W at least the canonical paper geometric cutoff, and a permitted mesh M with δ>0 and δ+η at most the canonical geometric tolerance, eventually n>1 and W≠0. For every scale-separation witness, its canonical partition P, with w=δ+η, has the following five bounds. Here V is the partition variance and E its center energy. The cutoff precedes the mesh; this supplies the geometric data for Lemma 8.6.
--
--   $$|\operatorname{dev}_p|\le w,\quad L_1\le7w,\quad w^2\le(456/c_{\rm Mesh}^2)V,\quad V\le4w^2,\quad V\le E.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalGeometricMomentFineMeshEventually.lean#L41-L173

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

theorem Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricCutoff_eventually :
∀ (cMesh : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) cMesh →
    ∀ (W : Nat),
      @LE.le.{0} Nat instLENat Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricCutoff W →
        ∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta)
          (hdelta :
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              delta),
          @Erdos390.Full.PaperPermittedRegularMesh.IsPermitted delta eta cMesh M →
            @LE.le.{0} Real Real.instLE
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) delta eta)
                Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance →
              @Filter.Eventually.{0} Nat
                (fun (n : Nat) =>
                  @Exists.{0} (@Ne.{1} Nat W (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    fun (hWne : @Ne.{1} Nat W (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) =>
                    @Exists.{0}
                      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
                      fun
                        (hn :
                          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n) =>
                      ∀ (S : @Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation delta eta M n W),
                        let P :=
                          @Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition delta eta M n W hdelta hn hWne
                            S;
                        And
                          (∀ (p : Erdos390.Full.ArithmeticBandGeometry.BandPrime n W),
                            @LE.le.{0} Real Real.instLE
                              (@abs.{0} Real Real.lattice Real.instAddGroup
                                (@Erdos390.Full.ArithmeticBandGeometry.Partition.deviation.{0} n W
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
                                  P p))
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) delta eta))
                          (And
                            (@LE.le.{0} Real Real.instLE
                              (@Erdos390.Full.ArithmeticBandGeometry.Partition.totalL1.{0} n W
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
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@OfNat.ofNat.{0} Real (nat_lit 7)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 7) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) delta eta)))
                            (And
                              (@LE.le.{0} Real Real.instLE
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat (@Monoid.toPow.{0} Real Real.instMonoid))
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) delta eta)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                    (@OfNat.ofNat.{0} Real (nat_lit 456)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 456) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 455) (instOfNatNat (nat_lit 455)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 454) (instOfNatNat (nat_lit 454)))))))
                                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                                      (@instHPow.{0, 0} Real Nat (@Monoid.toPow.{0} Real Real.instMonoid)) cMesh
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                  (@Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{0} n W
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
                              (And
                                (@LE.le.{0} Real Real.instLE
                                  (@Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{0} n W
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
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                                      (@instHPow.{0, 0} Real Nat (@Monoid.toPow.{0} Real Real.instMonoid))
                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) delta eta)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                                (@LE.le.{0} Real Real.instLE
                                  (@Erdos390.Full.ArithmeticBandGeometry.Partition.variance.{0} n W
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
                                    P))))))
                (@Filter.atTop.{0} Nat Nat.instPreorder) := by sorry
