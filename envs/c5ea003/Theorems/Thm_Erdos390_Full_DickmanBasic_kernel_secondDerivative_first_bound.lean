-- Prove2me | Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
-- name    : Erdos390.Full.DickmanBasic.kernel_secondDerivative_first_bound
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T13:44:07.469994+00:00
-- url     : https://prove2.me/theorems/ee53cf1b-e138-4f3b-9241-88944bf57606
-- title:
--   Uniform first-coordinate bound for the derivative of the Dickman covariance kernel
-- statement:
--   Let $\rho=\rho_5$ be the finite method-of-steps Dickman function, let $U=9/2$, and put $F(x)=\rho(U-x)/\rho(U)$. There is a real constant $C>0$ such that, for every pair of real numbers $s,t\in[0,1]$,
--
--   $$\left|F'(s+t)-F(s)F'(t)\right|\le Cs.$$
--
--   The derivative is the ordinary real derivative, represented by Lean's `deriv`. The estimate is uniform over the whole unit square, including the boundary $s=0$. It controls the derivative in the second variable of the normalized Dickman covariance kernel and its vanishing at the first-coordinate boundary.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/DickmanBasic.lean#L659-L739

import Definitions.Def_erdos390_dickman_step_function

theorem Erdos390.Full.DickmanBasic.kernel_secondDerivative_first_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |deriv Erdos390.Full.DickmanBasic.F (s + t) -
        Erdos390.Full.DickmanBasic.F s * deriv Erdos390.Full.DickmanBasic.F t| ≤ C * s := by sorry
