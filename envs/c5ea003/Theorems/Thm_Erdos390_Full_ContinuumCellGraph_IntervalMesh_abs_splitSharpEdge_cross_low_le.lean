-- Prove2me | Theorems.Thm_Erdos390_Full_ContinuumCellGraph_IntervalMesh_abs_splitSharpEdge_cross_low_le
-- name    : Erdos390.Full.ContinuumCellGraph.IntervalMesh.abs_splitSharpEdge_cross_low_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:01:51.778134+00:00
-- url     : https://prove2.me/theorems/21ff4950-1d6d-4ba3-9af3-9565fb65833f
-- title:
--   High-to-low cross-row bound for a split continuum mesh
-- statement:
--   Let M be a finite interval mesh with a splitting e: Low ⊕ High ≃ Band. Write α_x for its cell centers and ℓ_x for its cell lengths. Assume the normalized kernel cell is bounded by Cα_iℓ_j, with C ≥ 0; low centers are at most c₀ ≥ 0 and their total length at most L₀; high centers are at least a_min > 0. If |α_xq_x| ≤ B and |α_lq_l| ≤ b₀ on low cells, where B,b₀ ≥ 0, every high cell i satisfies the cross-row estimate below. The edge weights are the split sharp kernel edges. This separates the full raw norm from the smaller low-coordinate budget.
--
--   $$\left|\sum_{l\in\mathrm{Low}} E_{il}(q_i-q_l)\right|\le \frac{Cc_0L_0 B}{a_{\min}}+CL_0b_0.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/ContinuumManyLowHighGeometry.lean#L275-L378

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

theorem Erdos390.Full.ContinuumCellGraph.IntervalMesh.abs_splitSharpEdge_cross_low_le :
∀ {Band : Type u_1} {Low : Type u_2} {High : Type u_3} [inst : Fintype.{u_1} Band] [inst_1 : Fintype.{u_2} Low]
  {epsilon : Real} (M : Erdos390.Full.ContinuumCellGraph.IntervalMesh.{u_1} epsilon Band)
  (e : Equiv.{max (u_3 + 1) (u_2 + 1), u_1 + 1} (Sum.{u_2, u_3} Low High) Band)
  {C lowCenter lowLength amin B lowBudget : Real},
  LE.le.{0} (0 : Real) C →
    LE.le.{0} (0 : Real) lowCenter →
      LE.le.{0} (0 : Real) B →
        LE.le.{0} (0 : Real) lowBudget →
          (∀ (i j : Band),
              LE.le.{0} (abs.{0} (Erdos390.Full.ContinuumCellGraph.IntervalMesh.normalizedKernelCell.{u_1} M i j))
                (HMul.hMul.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0} C (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M i))
                  (Erdos390.Full.ContinuumCellGraph.IntervalMesh.length.{u_1} M j))) →
            (∀ (l : Low),
                LE.le.{0} (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e (Sum.inl.{u_2, u_3} l)))
                  lowCenter) →
              LE.le.{0} (∑ l, Erdos390.Full.ContinuumCellGraph.IntervalMesh.length.{u_1} M (e (Sum.inl.{u_2, u_3} l)))
                  lowLength →
                LT.lt.{0} (0 : Real) amin →
                  (∀ (i : High),
                      LE.le.{0} amin
                        (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e (Sum.inr.{u_2, u_3} i)))) →
                    ∀ (q : Sum.{u_2, u_3} Low High → Real),
                      (∀ (x : Sum.{u_2, u_3} Low High),
                          LE.le.{0}
                            (abs.{0}
                              (HMul.hMul.{0, 0, 0} (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M (e x))
                                (q x)))
                            B) →
                        (∀ (l : Low),
                            LE.le.{0}
                              (abs.{0}
                                (HMul.hMul.{0, 0, 0}
                                  (Erdos390.Full.ContinuumCellGraph.IntervalMesh.center.{u_1} M
                                    (e (Sum.inl.{u_2, u_3} l)))
                                  (q (Sum.inl.{u_2, u_3} l))))
                              lowBudget) →
                          ∀ (i : High),
                            LE.le.{0}
                              (abs.{0}
                                (∑ l,
                                  HMul.hMul.{0, 0, 0}
                                    (Erdos390.Full.ContinuumCellGraph.IntervalMesh.splitSharpEdge.{u_1, u_2, u_3} M e
                                      (Sum.inr.{u_2, u_3} i) (Sum.inl.{u_2, u_3} l))
                                    (HSub.hSub.{0, 0, 0} (q (Sum.inr.{u_2, u_3} i)) (q (Sum.inl.{u_2, u_3} l)))))
                              (HAdd.hAdd.{0, 0, 0}
                                (HDiv.hDiv.{0, 0, 0}
                                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C lowCenter) lowLength)
                                    B)
                                  amin)
                                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C lowLength) lowBudget)) := by sorry
