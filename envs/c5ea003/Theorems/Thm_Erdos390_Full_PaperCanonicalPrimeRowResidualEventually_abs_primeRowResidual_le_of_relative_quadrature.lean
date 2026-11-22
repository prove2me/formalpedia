-- Prove2me | Theorems.Thm_Erdos390_Full_PaperCanonicalPrimeRowResidualEventually_abs_primeRowResidual_le_of_relative_quadrature
-- name    : Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.abs_primeRowResidual_le_of_relative_quadrature
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:20:25.289529+00:00
-- url     : https://prove2.me/theorems/dc7ab97c-d762-428f-a9ff-262f28502334
-- title:
--   Relative first-moment quadrature controls the prime-row residual
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, and $\mathcal P=\{p\text{ prime}:W<p\le Y\}$. Assume $n>1$, $2\le W\le Y$, and $C\ge0$. Let $t_x=\log x/\log y$ and suppose $|K(u,t)|\le Cut$ on the unit square. Assume the prime quadrature for the first-moment kernel $\Phi(s,\cdot)$ over $(W,Y]$ differs from its harmonic integral by at most $Ds/(\log W)^3$ for every $s\in[0,1]$. For a band prime $p$, the residual $r_p=\mathrm{primeDiagonal}(p)+\sum_q\mathrm{primeWeight}(q)\mathrm{primeKernel}(p,q)$ satisfies
--
--   $$|r_p|\le\left(\frac D{(\log W)^3}+C(t_W+1-t_Y)\right)t_p.$$
--
--   The result attaches relative analytic quadrature directly to the literal finite row.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalPrimeRowResidualEventually.lean#L756-L869

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

theorem Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.abs_primeRowResidual_le_of_relative_quadrature :
∀ {D C : Real},
  LE.le.{0} (0 : Real) C →
    ∀ {n W : Nat},
      LT.lt.{0} (1 : Nat) n →
        LE.le.{0} (2 : Nat) W →
          LE.le.{0} W (Erdos390.Full.ArithmeticModel.yNat n) →
            (∀ (u : Real),
                Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) u →
                  ∀ (t : Real),
                    Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) t →
                      LE.le.{0} (abs.{0} (Erdos390.Full.ConditionedPoissonLimit.covarianceKernel u t))
                        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C u) t)) →
              (∀ (s : Real),
                  Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) s →
                    LE.le.{0}
                      (abs.{0}
                        (HSub.hSub.{0, 0, 0}
                          (Erdos390.Full.DoubleKernelPrimeQuadrature.primeCellOperator
                            (Erdos390.Full.ArithmeticModel.y n) W (Erdos390.Full.ArithmeticModel.yNat n)
                            (Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.firstMomentKernel s))
                          (∫ (t : Real) in
                            Erdos390.Full.KernelPrimeQuadrature.realLogCoordinate (Erdos390.Full.ArithmeticModel.y n)
                              ↑W..Erdos390.Full.KernelPrimeQuadrature.realLogCoordinate
                              (Erdos390.Full.ArithmeticModel.y n) ↑(Erdos390.Full.ArithmeticModel.yNat n),
                            HDiv.hDiv.{0, 0, 0}
                              (Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.firstMomentKernel s t) t)))
                      (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} D (HPow.hPow.{0, 0, 0} (Real.log ↑W) (3 : Nat))) s)) →
                ∀ (p : Erdos390.Full.PrimeSquarefreeDirichletGeometry.PrimeIndex n W),
                  LE.le.{0}
                    (abs.{0}
                      (Erdos390.Full.FiniteAnchoredDirichletQuadratic.rowResidual.{0}
                        (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight n)
                        (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeDiagonal n)
                        (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeKernel n) p))
                    (HMul.hMul.{0, 0, 0}
                      (Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.primeRowRelativeError D C n W)
                      (Erdos390.Full.ArithmeticModel.tPrime n ↑p)) := by sorry
