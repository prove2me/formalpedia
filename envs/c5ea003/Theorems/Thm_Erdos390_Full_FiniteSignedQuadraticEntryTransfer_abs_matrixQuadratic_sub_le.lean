-- Prove2me | Theorems.Thm_Erdos390_Full_FiniteSignedQuadraticEntryTransfer_abs_matrixQuadratic_sub_le
-- name    : Erdos390.Full.FiniteSignedQuadraticEntryTransfer.abs_matrixQuadratic_sub_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:02:46.23848+00:00
-- url     : https://prove2.me/theorems/158bb46a-837a-4ed7-a3cc-bd90d244261e
-- title:
--   Entrywise signed matrix errors control quadratic-form errors
-- statement:
--   Let $A,B$ be real matrices indexed by a finite set, and let $w_i,c_i$ be arbitrary real weights and coefficients. Suppose for every $i,j$,
--   $$|A_{ij}-B_{ij}|\le\epsilon_o w_iw_j+1_{i=j}(\epsilon_dw_i+\epsilon_2w_i^2).$$
--   Then
--   $$|c^TAc-c^TBc|\le\epsilon_o\left(\sum_iw_i|c_i|\right)^2+\epsilon_d\sum_iw_ic_i^2+\epsilon_2\sum_iw_i^2c_i^2.$$
--   No additional sign hypotheses are imposed: the asserted entrywise inequalities are the complete assumptions. This is the finite signed quadratic transfer with separate off-diagonal, first-weight diagonal, and second-weight diagonal budgets.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/FiniteSignedQuadraticEntryTransfer.lean#L34-L157

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_005

universe u_1

theorem Erdos390.Full.FiniteSignedQuadraticEntryTransfer.abs_matrixQuadratic_sub_le :
∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [inst_1 : DecidableEq.{u_1 + 1} ι] (A B : ι → ι → Real) (weight c : ι → Real)
  {epsilonOff epsilonDiag epsilonSecond : Real},
  (∀ (i j : ι),
      LE.le.{0} (abs.{0} (HSub.hSub.{0, 0, 0} (A i j) (B i j)))
        (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} epsilonOff (weight i)) (weight j))
          (ite.{1} (Eq.{u_1 + 1} i j)
            (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} epsilonDiag (weight i))
              (HMul.hMul.{0, 0, 0} epsilonSecond (HPow.hPow.{0, 0, 0} (weight i) (2 : Nat))))
            (0 : Real)))) →
    LE.le.{0}
      (abs.{0}
        (HSub.hSub.{0, 0, 0} (Erdos390.Full.FiniteSignedQuadraticEntryTransfer.matrixQuadratic.{u_1} A c)
          (Erdos390.Full.FiniteSignedQuadraticEntryTransfer.matrixQuadratic.{u_1} B c)))
      (HAdd.hAdd.{0, 0, 0}
        (HAdd.hAdd.{0, 0, 0}
          (HMul.hMul.{0, 0, 0} epsilonOff
            (HPow.hPow.{0, 0, 0} (Erdos390.Full.FiniteSignedQuadraticEntryTransfer.weightedL1.{u_1} weight c)
              (2 : Nat)))
          (HMul.hMul.{0, 0, 0} epsilonDiag
            (Erdos390.Full.FiniteSignedQuadraticEntryTransfer.weightedL2Sq.{u_1} weight c)))
        (HMul.hMul.{0, 0, 0} epsilonSecond
          (Erdos390.Full.FiniteSignedQuadraticEntryTransfer.weightedL2SqSecond.{u_1} weight c))) := by sorry
