-- Prove2me | Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
-- name    : Erdos390.Full.DickmanBasic.kernel_product_bound
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T13:46:37.547502+00:00
-- url     : https://prove2.me/theorems/b9e54de3-432b-44d2-bd2c-3eac3643b749
-- title:
--   Uniform quadratic product defect for the normalized Dickman kernel
-- statement:
--   Let $\rho=\rho_5$ be the finite method-of-steps Dickman function, $U=9/2$, and $F(x)=\rho(U-x)/\rho(U)$. There exists a real constant $C>0$ such that
--
--   $$\forall s,t\in[0,1],\qquad |F(s+t)-F(s)F(t)|\le Cst.$$
--
--   The bound is uniform up to both coordinate boundaries. It controls the normalized Dickman covariance kernel by a quadratic product weight, as required in the covariance-operator estimates.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/DickmanBasic.lean#L554-L657

import Definitions.Def_erdos390_dickman_step_function

theorem Erdos390.Full.DickmanBasic.kernel_product_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |Erdos390.Full.DickmanBasic.F (s + t) -
        Erdos390.Full.DickmanBasic.F s * Erdos390.Full.DickmanBasic.F t| ≤ C * s * t := by sorry
