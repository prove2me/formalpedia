-- Prove2me | Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_momentReady_of_endpointMomentBounds
-- name    : Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.momentReady_of_endpointMomentBounds
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:28:02.589128+00:00
-- url     : https://prove2.me/theorems/06ba6cb4-65a3-4b56-87d9-acc729b6c927
-- title:
--   Endpoint PNT bounds imply regular-mesh moment readiness
-- statement:
--   Let $M$ be a regular relative mesh and $P$ its prime partition with endpoints given by the canonical floored cutoffs. Suppose $W\ge8$ dominates the three thresholds $X_0,X_1,X_2$. For all integer $X_j\le A\le Y$, assume the reciprocal prime mass error is at most $5C_0/(\log A)^3$, the log-weighted reciprocal error is at most $2C_1/(\log A)^3+C_1/(2(\log A)^2)$, and, for all $z>1$, the squared logarithmic-coordinate error is at most $3C_2/((\log z)^2\log A)$. Their main terms are respectively $\log\log Y-\log\log A$, $\log Y-\log A$, and $((\log Y/\log z)^2-(\log A/\log z)^2)/2$. Assume $n>1$ and the endpoint inequalities in $\mathrm{EndpointMomentBounds}(M,n,W,C_0,C_1,C_2)$: positive-cell main mass at most twice the mesh ratio with error at most that ratio; low first-moment main term at most $3\delta/2$ with error at most $\delta/2$; low second-moment main term between $5\delta^2/12$ and $11\delta^2/12$ with error at most $\delta^2/12$; and low main mass at least $48$ plus its mass error. Then the partition is moment-ready:
--
--   $$\operatorname{mass}(k+1)\le3\operatorname{ratio}(M),\quad \operatorname{mass}(0)\operatorname{center}(0)\le2\delta,\quad \frac{\delta^2}{3}\le\operatorname{secondMoment}(0)\le\delta^2,\quad\operatorname{mass}(0)\ge48.$$
--
--   This separates deterministic moment assembly from the eventual analytic selection of its thresholds.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/RegularMeshActualMomentBoundsEventually.lean#L340-L502

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

theorem Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.momentReady_of_endpointMomentBounds :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) {n W : Nat}
  (P :
    Erdos390.Full.ArithmeticBandGeometry.Partition.{0} n W
      (Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))))
  (E : Erdos390.Full.PositiveCellTransfer.IntervalCertificate.{0} P),
  (∀ (j : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))),
      Eq.{1} (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{0} E j)
        (Erdos390.Full.RegularMeshPrimeCutoffs.fullCutoff M n W ↑j)) →
    (∀ (j : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))),
        Eq.{1} (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{0} E j)
          (Erdos390.Full.RegularMeshPrimeCutoffs.fullCutoff M n W (HAdd.hAdd.{0, 0, 0} ↑j (1 : Nat)))) →
      ∀ {Cmass Cfirst Csecond : Real} {Xmass Xfirst Xsecond : Nat},
        LE.le.{0} (8 : Nat) W →
          LE.le.{0} Xmass W →
            LE.le.{0} Xfirst W →
              LE.le.{0} Xsecond W →
                (∀ (A Y : Nat),
                    LE.le.{0} Xmass A →
                      LE.le.{0} A Y →
                        LE.le.{0}
                          (abs.{0}
                            (HSub.hSub.{0, 0, 0}
                              (HSub.hSub.{0, 0, 0} (Erdos390.Full.PrimeSums.fullReciprocalSum Y)
                                (Erdos390.Full.PrimeSums.fullReciprocalSum A))
                              (HSub.hSub.{0, 0, 0} (Real.log (Real.log ↑Y)) (Real.log (Real.log ↑A)))))
                          (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (5 : Real) Cmass)
                            (HPow.hPow.{0, 0, 0} (Real.log ↑A) (3 : Nat)))) →
                  (∀ (A Y : Nat),
                      LE.le.{0} Xfirst A →
                        LE.le.{0} A Y →
                          LE.le.{0}
                            (abs.{0}
                              (HSub.hSub.{0, 0, 0}
                                (HSub.hSub.{0, 0, 0} (Erdos390.Full.PrimeSums.fullLogReciprocalSum Y)
                                  (Erdos390.Full.PrimeSums.fullLogReciprocalSum A))
                                (HSub.hSub.{0, 0, 0} (Real.log ↑Y) (Real.log ↑A))))
                            (HAdd.hAdd.{0, 0, 0}
                              (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) Cfirst)
                                (HPow.hPow.{0, 0, 0} (Real.log ↑A) (3 : Nat)))
                              (HDiv.hDiv.{0, 0, 0} Cfirst
                                (HMul.hMul.{0, 0, 0} (2 : Real) (HPow.hPow.{0, 0, 0} (Real.log ↑A) (2 : Nat)))))) →
                    (∀ (z : Real),
                        LT.lt.{0} (1 : Real) z →
                          ∀ (A Y : Nat),
                            LE.le.{0} Xsecond A →
                              LE.le.{0} A Y →
                                LE.le.{0}
                                  (abs.{0}
                                    (HSub.hSub.{0, 0, 0}
                                      (HSub.hSub.{0, 0, 0}
                                        (Erdos390.Full.KernelPrimeQuadrature.fullWeightedReciprocalSum
                                          Erdos390.Full.PrimeCoordinateSecondMoment.squareCoordinate z Y)
                                        (Erdos390.Full.KernelPrimeQuadrature.fullWeightedReciprocalSum
                                          Erdos390.Full.PrimeCoordinateSecondMoment.squareCoordinate z A))
                                      (HDiv.hDiv.{0, 0, 0}
                                        (HSub.hSub.{0, 0, 0}
                                          (HPow.hPow.{0, 0, 0}
                                            (Erdos390.Full.KernelPrimeQuadrature.realLogCoordinate z ↑Y) (2 : Nat))
                                          (HPow.hPow.{0, 0, 0}
                                            (Erdos390.Full.KernelPrimeQuadrature.realLogCoordinate z ↑A) (2 : Nat)))
                                        (2 : Real))))
                                  (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (3 : Real) Csecond)
                                    (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Real.log z) (2 : Nat)) (Real.log ↑A)))) →
                      Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.EndpointMomentBounds M n W Cmass Cfirst Csecond →
                        Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.MomentReady M P := by sorry
