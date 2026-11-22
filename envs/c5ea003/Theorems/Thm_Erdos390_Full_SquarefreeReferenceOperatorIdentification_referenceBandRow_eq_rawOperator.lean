-- Prove2me | Theorems.Thm_Erdos390_Full_SquarefreeReferenceOperatorIdentification_referenceBandRow_eq_rawOperator
-- name    : Erdos390.Full.SquarefreeReferenceOperatorIdentification.referenceBandRow_eq_rawOperator
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:50:35.130777+00:00
-- url     : https://prove2.me/theorems/0f3dda54-6a91-4a20-b5b5-0de347e66e85
-- title:
--   The reference band row is the raw arithmetic operator
-- statement:
--   For a partition $P$ of the moving prime band and an interval certificate identifying its prime fibers, let $D_i$ and $K_{ij}$ be the associated compressed arithmetic diagonal and kernel. Then every real band vector $b$ satisfies
--   $$\operatorname{ReferenceBandRow}(P,b)_i=D_i b_i+\sum_jK_{ij}b_j.$$
--   Thus the prime-level reference row is exactly the raw arithmetic operator, with no approximation error. The moving prime band is $\{p\text{ prime}:W<p\le\lfloor n^{2/9}\rfloor\}$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/SquarefreeReferenceOperatorIdentification.lean#L224-L337

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

theorem Erdos390.Full.SquarefreeReferenceOperatorIdentification.referenceBandRow_eq_rawOperator :
∀ {n W : Nat} {Band : Type u_1} [inst : Fintype.{u_1} Band] [inst_1 : DecidableEq.{u_1 + 1} Band]
  {P : Erdos390.Full.ArithmeticBandGeometry.Partition.{u_1} n W Band}
  (E : Erdos390.Full.PositiveCellTransfer.IntervalCertificate.{u_1} P) (b : Band → Real) (i : Band),
  Eq.{1} (Erdos390.Full.SquarefreeSharpBandTransfer.referenceBandRow.{u_1} P b i)
    (Erdos390.Full.PaperWeightedInverseExport.rawOperator.{u_1}
      (Erdos390.Full.CompressedArithmeticOperator.arithmeticDiagonal.{u_1} (Erdos390.Full.ArithmeticModel.y n)
        (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_1} E)
        (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_1} E))
      (Erdos390.Full.CompressedArithmeticOperator.arithmeticKernel.{u_1} (Erdos390.Full.ArithmeticModel.y n)
        (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.lower.{u_1} E)
        (Erdos390.Full.PositiveCellTransfer.IntervalCertificate.upper.{u_1} E))
      b i) := by sorry
