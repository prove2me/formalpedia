-- Prove2me | Theorems.Thm_Erdos390_Full_DoubleKernelPrimeQuadrature_doubleKernelCell_error_le_of_oneIndex
-- name    : Erdos390.Full.DoubleKernelPrimeQuadrature.doubleKernelCell_error_le_of_oneIndex
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T14:54:02.271745+00:00
-- url     : https://prove2.me/theorems/7a06daf6-004d-4d5b-b99b-40dbf5388d0f
-- title:
--   Two-index quadrature from uniform one-index errors
-- statement:
--   Let $z>1$ and $2\le A_i\le Y_i\le z$ for $i=1,2$. Write $t_x=\log x/\log z$, $P_i f=\sum_{A_i<p\le Y_i}f(t_p)/p$, and $C_i f=\int_{t_{A_i}}^{t_{Y_i}}f(t)\,dt/t$. For the covariance kernel $K$, suppose $|P_i(K(t,\cdot))-C_i(K(t,\cdot))|\le e_i$ uniformly for $t\in[0,1]$. Let $PPK$ and $CCK$ denote the corresponding double prime and double continuum kernel cells.
--
--   $$|PPK-CCK|\le e_2\sum_{A_1<p\le Y_1}\frac1p+e_1\log\frac{t_{Y_2}}{t_{A_2}}.$$
--
--   This transfers one-dimensional PNT quadrature to the double kernel cells used in matrix estimates.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/DoubleKernelPrimeQuadrature.lean#L346-L462

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

theorem Erdos390.Full.DoubleKernelPrimeQuadrature.doubleKernelCell_error_le_of_oneIndex :
∀ {z : Real},
  LT.lt.{0} (1 : Real) z →
    ∀ {A₁ Y₁ A₂ Y₂ : Nat},
      LE.le.{0} (2 : Nat) A₁ →
        LE.le.{0} A₁ Y₁ →
          LE.le.{0} (↑Y₁) z →
            LE.le.{0} (2 : Nat) A₂ →
              LE.le.{0} A₂ Y₂ →
                LE.le.{0} (↑Y₂) z →
                  ∀ {e₁ e₂ : Real},
                    (∀ (t : Real),
                        Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) t →
                          LE.le.{0}
                            (abs.{0}
                              (HSub.hSub.{0, 0, 0}
                                (Erdos390.Full.DoubleKernelPrimeQuadrature.primeCellOperator z A₁ Y₁
                                  (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel t))
                                (Erdos390.Full.DoubleKernelPrimeQuadrature.continuumCellOperator z A₁ Y₁
                                  (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel t))))
                            e₁) →
                      (∀ (s : Real),
                          Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) s →
                            LE.le.{0}
                              (abs.{0}
                                (HSub.hSub.{0, 0, 0}
                                  (Erdos390.Full.DoubleKernelPrimeQuadrature.primeCellOperator z A₂ Y₂
                                    (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel s))
                                  (Erdos390.Full.DoubleKernelPrimeQuadrature.continuumCellOperator z A₂ Y₂
                                    (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel s))))
                              e₂) →
                        LE.le.{0}
                          (abs.{0}
                            (HSub.hSub.{0, 0, 0}
                              (Erdos390.Full.DoubleKernelPrimeQuadrature.doublePrimeKernelCell z A₁ Y₁ A₂ Y₂)
                              (Erdos390.Full.DoubleKernelPrimeQuadrature.doubleContinuumKernelCell z A₁ Y₁ A₂ Y₂)))
                          (HAdd.hAdd.{0, 0, 0}
                            (HMul.hMul.{0, 0, 0} e₂
                              (HSub.hSub.{0, 0, 0} (Erdos390.Full.PrimeSums.fullReciprocalSum Y₁)
                                (Erdos390.Full.PrimeSums.fullReciprocalSum A₁)))
                            (HMul.hMul.{0, 0, 0} e₁
                              (HSub.hSub.{0, 0, 0}
                                (Real.log (Erdos390.Full.KernelPrimeQuadrature.realLogCoordinate z ↑Y₂))
                                (Real.log (Erdos390.Full.KernelPrimeQuadrature.realLogCoordinate z ↑A₂))))) := by sorry
