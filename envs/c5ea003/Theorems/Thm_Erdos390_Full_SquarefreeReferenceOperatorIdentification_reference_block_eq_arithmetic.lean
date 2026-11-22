-- Prove2me | Theorems.Thm_Erdos390_Full_SquarefreeReferenceOperatorIdentification_reference_block_eq_arithmetic
-- name    : Erdos390.Full.SquarefreeReferenceOperatorIdentification.reference_block_eq_arithmetic
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:29:36.633062+00:00
-- url     : https://prove2.me/theorems/889b2622-2e1c-4b4b-8a50-084e99c99d24
-- title:
--   Reference covariance blocks equal the compressed arithmetic matrix
-- statement:
--   Let $P$ be a partition of the moving prime band, with harmonic mass $m_i$, and let an interval certificate identify its fibers $P_i$ with the source's arithmetic prime cells. Write $D_i$ and $K_{ij}$ for the corresponding compressed arithmetic diagonal and kernel at scale $y(n)$, and $R_{pq}$ for the squarefree reference entries. Then for all bands $i,j$,
--   $$\frac1{m_i}\sum_{p\in P_i}\sum_{q\in P_j}R_{pq}=K_{ij}+1_{i=j}D_i.$$
--   This identifies the signed probabilistic reference with the arithmetic matrix used in the inverse estimates. The moving prime band is $\{p\text{ prime}:W<p\le\lfloor n^{2/9}\rfloor\}$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/SquarefreeReferenceOperatorIdentification.lean#L121-L222

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

universe u_1

theorem Erdos390.Full.SquarefreeReferenceOperatorIdentification.reference_block_eq_arithmetic :
∀ {n W : Nat} {Band : Type u_1} [inst : Fintype.{u_1} Band] [inst_1 : DecidableEq.{u_1 + 1} Band]
  {P : Erdos390.Full.ArithmeticBandGeometry.Partition.{u_1} n W Band}
  (E : Erdos390.Full.PositiveCellTransfer.IntervalCertificate.{u_1} P) (i j : Band),
  Eq.{1}
    (HMul.hMul.{0, 0, 0}
      (HDiv.hDiv.{0, 0, 0} (1 : Real) (Erdos390.Full.ArithmeticBandGeometry.Partition.mass.{u_1} P i))
      (∑
        p ∈
          Erdos390.Lemma84.WeightedBandData.fiber.{0, u_1} (Erdos390.Full.ArithmeticBandGeometry.Partition.data.{u_1} P)
            i,
        ∑
          q ∈
            Erdos390.Lemma84.WeightedBandData.fiber.{0, u_1}
              (Erdos390.Full.ArithmeticBandGeometry.Partition.data.{u_1} P) j,
          Erdos390.Full.SquarefreeCovarianceReference.squarefreeReferenceEntry n ↑p ↑q))
    (HAdd.hAdd.{0, 0, 0}
      (Erdos390.Full.CompressedArithmeticOperator.arithmeticKernel.{u_1} (Erdos390.Full.ArithmeticModel.y n)
        (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_1} E)
        (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_1} E) i j)
      (ite.{1} (Eq.{u_1 + 1} i j)
        (Erdos390.Full.CompressedArithmeticOperator.arithmeticDiagonal.{u_1} (Erdos390.Full.ArithmeticModel.y n)
          (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_1} E)
          (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_1} E) i)
        (0 : Real))) := by sorry
