-- Prove2me | Theorems.Thm_Erdos390_Full_KernelPrimeQuadrature_abs_kernelWeightedAbelRemainder_le
-- name    : Erdos390.Full.KernelPrimeQuadrature.abs_kernelWeightedAbelRemainder_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T14:50:07.519884+00:00
-- url     : https://prove2.me/theorems/99be79ce-16e9-4c14-b4ed-595edfb48b27
-- title:
--   Uniform Abel remainder for the covariance kernel
-- statement:
--   Let $C,M\ge0$, $s\in[0,1]$, $z>1$, and integers $2\le A\le Y\le z$. Suppose the covariance kernel $K$ and its extended second-coordinate derivative have absolute value at most $M$ on $[0,1]^2$. Suppose the Chebyshev error satisfies $|\theta(x)-x|\le Cx/(\log x)^3$ on $[A,Y]$. Let $R$ be the weighted Abel remainder for $K(s,\cdot)$ with logarithmic coordinate $\log x/\log z$.
--
--   $$|R|\le\frac{6CM}{(\log A)^3}.$$
--
--   The resulting constant is uniform in the first kernel coordinate and in the moving cell endpoints.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/KernelPrimeQuadrature.lean#L918-L1082

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_003

theorem Erdos390.Full.KernelPrimeQuadrature.abs_kernelWeightedAbelRemainder_le :
∀ {C M s z : Real},
  LE.le.{0} (0 : Real) C →
    LE.le.{0} (0 : Real) M →
      Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) s →
        LT.lt.{0} (1 : Real) z →
          ∀ {A Y : Nat},
            LE.le.{0} (2 : Nat) A →
              LE.le.{0} A Y →
                LE.le.{0} (↑Y) z →
                  (∀ (u : Real),
                      Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) u →
                        ∀ (v : Real),
                          Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) v →
                            And (LE.le.{0} (abs.{0} (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel u v)) M)
                              (LE.le.{0}
                                (abs.{0}
                                  (Erdos390.Full.KernelPrimeQuadrature.covarianceKernelDerivativeSecondExtension u v))
                                M)) →
                    (∀ (x : Real),
                        Membership.mem.{0, 0} (Set.Icc.{0} ↑A ↑Y) x →
                          LE.le.{0} (abs.{0} (Erdos390.Full.PrimeBandQuadrature.thetaError x))
                            (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} C x)
                              (HPow.hPow.{0, 0, 0} (Real.log x) (3 : Nat)))) →
                      LE.le.{0}
                        (abs.{0}
                          (Erdos390.Full.KernelPrimeQuadrature.weightedAbelRemainder
                            (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel s) z ↑A ↑Y))
                        (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (6 : Real) (HMul.hMul.{0, 0, 0} C M))
                          (HPow.hPow.{0, 0, 0} (Real.log ↑A) (3 : Nat))) := by sorry
