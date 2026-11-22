-- Prove2me | Theorems.Thm_Erdos390_Full_ContinuumCellGraph_ArithmeticGaugeOrdinary_IntervalMesh_ordinary_split_arithmetic_projected_raw_bound
-- name    : Erdos390.Full.ContinuumCellGraph.ArithmeticGaugeOrdinary.IntervalMesh.ordinary_split_arithmetic_projected_raw_bound
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:10:45.600501+00:00
-- url     : https://prove2.me/theorems/da45d9dc-d250-4ff2-b374-d8a155f4cb2d
-- title:
--   Many-low ordinary inverse on the arithmetic raw gauge
-- statement:
--   Let a finite nonempty interval mesh be split into Low and nonempty High. Assume the covariance kernel product bound Cst, a positive interior quotient gap κ, positive high anchor mass A, high centers between a_min>0 and a_max≥0, low centers at most c₀≥0, and low and total lengths at most L₀,L≥0. Let positive arithmetic weights H_i and centers α_i≤α_max define the raw gauge. Assume the mixed low/high gauge ratio is bounded by g; low continuum diagonal error is at most d<1; continuum row residual is bounded by r≥0; arithmetic-versus-continuum raw row error is bounded by e‖b‖ with e≥0. With S=∑H_iα_i², assume α_max∑H_iα_i≤RS, R≥0, and α_max∑|H_iα_i−M.harmonicMass_i M.center_i|≤ρS with ρ≤1/2. Define ε=(r+Cc₀L)/(1−d), c=(1−d)⁻¹ and C₀=max(c,a_max[2(κA)⁻¹(a_min⁻¹+CL₀c)+gc]). Assume max(ε,a_max[2(κA)⁻¹(Cc₀L₀/a_min+CL₀ε)+gε])≤1/2 and 4C₀(1+R)(e+r)≤1/2. Then the projected arithmetic raw operator T satisfies the following bound. It is independent of the number and least center of the low cells.
--
--   $$\|b\|_\infty\le 8C_0\|Tb\|_\infty.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/ContinuumManyLowArithmeticGaugeOrdinary.lean#L192-L637

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

universe u_1 u_2 u_3

theorem Erdos390.Full.ContinuumCellGraph.ArithmeticGaugeOrdinary.IntervalMesh.ordinary_split_arithmetic_projected_raw_bound :
∀ {Band : Type u_1} {Low : Type u_2} {High : Type u_3} [inst : Fintype.{u_1} Band] [inst_1 : Fintype.{u_2} Low]
  [inst_2 : Fintype.{u_3} High] {epsilon : Real} (M : Erdos390.Full.ContinuumCellGraph.IntervalMesh.{u_1} epsilon Band)
  [inst_3 : DecidableEq.{u_1 + 1} Band] [inst_4 : Nonempty.{u_1 + 1} Band] [Nonempty.{u_3 + 1} High]
  (e : Equiv.{max (u_3 + 1) (u_2 + 1), u_1 + 1} (Sum.{u_2, u_3} Low High) Band) (diagonalA : Band → Real)
  (kernelA : Band → Band → Real) (H alphaA : Band → Real)
  {C kappa amin amax alphaAMax lowCenter lowLength totalLength gaugeRatio d residual rowError R rho : Real},
  LE.le.{0} (0 : Real) C →
    (∀ (s : Real),
        Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) s →
          ∀ (t : Real),
            Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) t →
              LE.le.{0} (abs.{0} (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel s t))
                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C s) t)) →
      LT.lt.{0} (0 : Real) kappa →
        (∀ (s : Real),
            Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) s →
              ∀ (t : Real),
                Membership.mem.{0, 0} (Set.Icc.{0} epsilon (HSub.hSub.{0, 0, 0} (1 : Real) epsilon)) t →
                  LE.le.{0} kappa (Neg.neg.{0} (Erdos390.Full.ConditionedPoissonLimit.covarianceKernelQuotient t s))) →
          LT.lt.{0} (0 : Real)
              (∑ i, Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitHighAnchor.{u_1, u_2, u_3} M e i) →
            LT.lt.{0} (0 : Real) amin →
              (∀ (i : High),
                  LE.le.{0} amin
                    (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e (Sum.inr.{u_2, u_3} i)))) →
                (∀ (i : High),
                    LE.le.{0} (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e (Sum.inr.{u_2, u_3} i)))
                      amax) →
                  LE.le.{0} (0 : Real) amax →
                    LE.le.{0} (0 : Real) lowCenter →
                      (∀ (l : Low),
                          LE.le.{0}
                            (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e (Sum.inl.{u_2, u_3} l)))
                            lowCenter) →
                        LE.le.{0} (0 : Real) lowLength →
                          LE.le.{0}
                              (∑ l,
                                Erdos390.Full.ContinuumCellGraph.IntervalMesh.length.{u_1} M (e (Sum.inl.{u_2, u_3} l)))
                              lowLength →
                            LE.le.{0} (0 : Real) totalLength →
                              LE.le.{0} (∑ i, Erdos390.Full.ContinuumCellGraph.IntervalMesh.length.{u_1} M i)
                                  totalLength →
                                ∀ (hH : ∀ (i : Band), LT.lt.{0} (0 : Real) (H i))
                                  (hAlphaA : ∀ (i : Band), LT.lt.{0} (0 : Real) (alphaA i)),
                                  (∀ (i : Band), LE.le.{0} (alphaA i) alphaAMax) →
                                    LE.le.{0}
                                        (∑ l,
                                          HMul.hMul.{0, 0, 0} (H (e (Sum.inl.{u_2, u_3} l)))
                                            (alphaA (e (Sum.inl.{u_2, u_3} l))))
                                        (HMul.hMul.{0, 0, 0} gaugeRatio
                                          (∑ i,
                                            HMul.hMul.{0, 0, 0}
                                              (HMul.hMul.{0, 0, 0} (H (e (Sum.inr.{u_2, u_3} i)))
                                                (alphaA (e (Sum.inr.{u_2, u_3} i))))
                                              (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M
                                                (e (Sum.inr.{u_2, u_3} i))))) →
                                      LT.lt.{0} d (1 : Real) →
                                        (∀ (l : Low),
                                            LE.le.{0}
                                              (abs.{0}
                                                (HSub.hSub.{0, 0, 0}
                                                  (Erdos390.Full.ContinuumCellGraph.IntervalMesh.normalizedDiagonalCell.{u_1}
                                                    M (e (Sum.inl.{u_2, u_3} l)))
                                                  (1 : Real)))
                                              d) →
                                          LE.le.{0} (0 : Real) residual →
                                            (∀ (i : Band),
                                                LE.le.{0}
                                                  (abs.{0}
                                                    (Erdos390.Full.ContinuumCellGraph.IntervalMesh.rowResidual.{u_1} M
                                                      i))
                                                  residual) →
                                              LE.le.{0} (0 : Real) rowError →
                                                (∀
                                                    (b :
                                                      ↥(Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{u_1} H
                                                          alphaA))
                                                    (i : Band),
                                                    LE.le.{0}
                                                      (abs.{0}
                                                        (HSub.hSub.{0, 0, 0}
                                                          (Erdos390.Full.PaperWeightedInverseExport.rawOperator.{u_1}
                                                            diagonalA kernelA (↑b) i)
                                                          (Erdos390.Full.PaperWeightedInverseExport.rawOperator.{u_1}
                                                            (Erdos390.Full.ContinuumCellGraph.IntervalMesh.normalizedDiagonalCell.{u_1}
                                                              M)
                                                            (Erdos390.Full.ContinuumCellGraph.IntervalMesh.normalizedKernelCell.{u_1}
                                                              M)
                                                            (↑b) i)))
                                                      (HMul.hMul.{0, 0, 0} rowError (Norm.norm.{u_1} b))) →
                                                  LE.le.{0} (0 : Real) R →
                                                    LE.le.{0}
                                                        (HMul.hMul.{0, 0, 0} alphaAMax
                                                          (∑ i, HMul.hMul.{0, 0, 0} (H i) (alphaA i)))
                                                        (HMul.hMul.{0, 0, 0} R
                                                          (Erdos390.Full.MovingLowGaugeTransfer.sharpWeightTotal.{u_1} H
                                                            alphaA)) →
                                                      LE.le.{0} rho (1 / 2 : Real) →
                                                        LE.le.{0}
                                                            (HMul.hMul.{0, 0, 0} alphaAMax
                                                              (∑ i,
                                                                abs.{0}
                                                                  (HSub.hSub.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0} (H i) (alphaA i))
                                                                    (HMul.hMul.{0, 0, 0}
                                                                      (Erdos390.Full.ContinuumCellGraph.IntervalMesh.harmonicMass.{u_1}
                                                                        M i)
                                                                      (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1}
                                                                        M i)))))
                                                            (HMul.hMul.{0, 0, 0} rho
                                                              (Erdos390.Full.MovingLowGaugeTransfer.sharpWeightTotal.{u_1}
                                                                H alphaA)) →
                                                          (have epsLow :=
                                                              HDiv.hDiv.{0, 0, 0}
                                                                (HAdd.hAdd.{0, 0, 0} residual
                                                                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C lowCenter)
                                                                    totalLength))
                                                                (HSub.hSub.{0, 0, 0} (1 : Real) d);
                                                            LE.le.{0}
                                                              (Max.max.{0} epsLow
                                                                (HMul.hMul.{0, 0, 0} amax
                                                                  (HAdd.hAdd.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0}
                                                                      (HMul.hMul.{0, 0, 0} (2 : Real)
                                                                        (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                          (HMul.hMul.{0, 0, 0} kappa
                                                                            (∑ i,
                                                                              Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitHighAnchor.{u_1,
                                                                                  u_2, u_3}
                                                                                M e i))))
                                                                      (HAdd.hAdd.{0, 0, 0}
                                                                        (HDiv.hDiv.{0, 0, 0}
                                                                          (HMul.hMul.{0, 0, 0}
                                                                            (HMul.hMul.{0, 0, 0} C lowCenter) lowLength)
                                                                          amin)
                                                                        (HMul.hMul.{0, 0, 0}
                                                                          (HMul.hMul.{0, 0, 0} C lowLength) epsLow)))
                                                                    (HMul.hMul.{0, 0, 0} gaugeRatio epsLow))))
                                                              (1 / 2 : Real)) →
                                                            (have Clow :=
                                                                HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                  (HSub.hSub.{0, 0, 0} (1 : Real) d);
                                                              have Cmain :=
                                                                Max.max.{0} Clow
                                                                  (HMul.hMul.{0, 0, 0} amax
                                                                    (HAdd.hAdd.{0, 0, 0}
                                                                      (HMul.hMul.{0, 0, 0}
                                                                        (HMul.hMul.{0, 0, 0} (2 : Real)
                                                                          (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                            (HMul.hMul.{0, 0, 0} kappa
                                                                              (∑ i,
                                                                                Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitHighAnchor.{u_1,
                                                                                    u_2, u_3}
                                                                                  M e i))))
                                                                        (HAdd.hAdd.{0, 0, 0}
                                                                          (HDiv.hDiv.{0, 0, 0} (1 : Real) amin)
                                                                          (HMul.hMul.{0, 0, 0}
                                                                            (HMul.hMul.{0, 0, 0} C lowLength) Clow)))
                                                                      (HMul.hMul.{0, 0, 0} gaugeRatio Clow)));
                                                              LE.le.{0}
                                                                (HMul.hMul.{0, 0, 0}
                                                                  (HMul.hMul.{0, 0, 0} (4 : Real) Cmain)
                                                                  (HMul.hMul.{0, 0, 0}
                                                                    (HAdd.hAdd.{0, 0, 0} (1 : Real) R)
                                                                    (HAdd.hAdd.{0, 0, 0} rowError residual)))
                                                                (1 / 2 : Real)) →
                                                              ∀
                                                                (b :
                                                                  ↥(Erdos390.Full.PaperWeightedInverseExport.RawGaugeSpace.{u_1}
                                                                      H alphaA)),
                                                                LE.le.{0} (Norm.norm.{u_1} b)
                                                                  (HMul.hMul.{0, 0, 0}
                                                                    (HMul.hMul.{0, 0, 0} (8 : Real)
                                                                      (Max.max.{0}
                                                                        (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                          (HSub.hSub.{0, 0, 0} (1 : Real) d))
                                                                        (HMul.hMul.{0, 0, 0} amax
                                                                          (HAdd.hAdd.{0, 0, 0}
                                                                            (HMul.hMul.{0, 0, 0}
                                                                              (HMul.hMul.{0, 0, 0} (2 : Real)
                                                                                (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                                  (HMul.hMul.{0, 0, 0} kappa
                                                                                    (∑ i,
                                                                                      Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitHighAnchor.{u_1,
                                                                                          u_2, u_3}
                                                                                        M e i))))
                                                                              (HAdd.hAdd.{0, 0, 0}
                                                                                (HDiv.hDiv.{0, 0, 0} (1 : Real) amin)
                                                                                (HMul.hMul.{0, 0, 0}
                                                                                  (HMul.hMul.{0, 0, 0} C lowLength)
                                                                                  (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                                    (HSub.hSub.{0, 0, 0} (1 : Real)
                                                                                      d)))))
                                                                            (HMul.hMul.{0, 0, 0} gaugeRatio
                                                                              (HDiv.hDiv.{0, 0, 0} (1 : Real)
                                                                                (HSub.hSub.{0, 0, 0} (1 : Real) d)))))))
                                                                    (Norm.norm.{u_1}
                                                                      ((Erdos390.Full.PaperWeightedInverseExport.projectedRawLinearMap.{u_1}
                                                                          diagonalA kernelA H alphaA
                                                                          (ne_of_gt.{0}
                                                                            (id.{0}
                                                                              (id.{0}
                                                                                (Finset.sum_pos.{u_1, 0}
                                                                                  (fun i _hi =>
                                                                                    mul_pos.{0} (hH i)
                                                                                      (sq_pos_of_pos.{0} (hAlphaA i)))
                                                                                  Finset.univ_nonempty.{u_1})))))
                                                                        b))) := by sorry
