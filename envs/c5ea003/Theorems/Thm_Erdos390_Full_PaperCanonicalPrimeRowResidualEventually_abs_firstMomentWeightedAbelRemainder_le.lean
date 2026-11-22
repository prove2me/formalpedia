-- Prove2me | Theorems.Thm_Erdos390_Full_PaperCanonicalPrimeRowResidualEventually_abs_firstMomentWeightedAbelRemainder_le
-- name    : Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.abs_firstMomentWeightedAbelRemainder_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:20:16.230718+00:00
-- url     : https://prove2.me/theorems/2e4968a0-5edc-4f1a-8e2d-7048deb2b529
-- title:
--   First-moment Abel remainder retains its row coordinate
-- statement:
--   Let $C,M\ge0$, $s\in[0,1]$, $z>1$, and $2\le A\le Y\le z$ with natural endpoints. Suppose the first-moment kernel $\Phi$ and its second-coordinate derivative obey $|\Phi(u,t)|,|\partial_t\Phi(u,t)|\le Mu$ on the unit square. Suppose $|\theta(x)-x|\le Cx/(\log x)^3$ on $[A,Y]$. Then the weighted Abel remainder satisfies
--
--   $$|R(\Phi(s,\cdot),z,A,Y)|\le\frac{6CMs}{(\log A)^3}.$$
--
--   Keeping the first coordinate explicit is essential for a relative prime-row error.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalPrimeRowResidualEventually.lean#L395-L557

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_005

theorem Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.abs_firstMomentWeightedAbelRemainder_le :
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
                        ∀ (t : Real),
                          Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) t →
                            LE.le.{0}
                              (abs.{0} (Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.firstMomentKernel u t))
                              (HMul.hMul.{0, 0, 0} M u)) →
                    (∀ (u : Real),
                        Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) u →
                          ∀ (t : Real),
                            Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real)) t →
                              LE.le.{0}
                                (abs.{0}
                                  (Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.firstMomentKernelDerivative u
                                    t))
                                (HMul.hMul.{0, 0, 0} M u)) →
                      (∀ (x : Real),
                          Membership.mem.{0, 0} (Set.Icc.{0} ↑A ↑Y) x →
                            LE.le.{0} (abs.{0} (Erdos390.Full.PrimeBandQuadrature.thetaError x))
                              (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} C x)
                                (HPow.hPow.{0, 0, 0} (Real.log x) (3 : Nat)))) →
                        LE.le.{0}
                          (abs.{0}
                            (Erdos390.Full.KernelPrimeQuadrature.weightedAbelRemainder
                              (Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.firstMomentKernel s) z ↑A ↑Y))
                          (HDiv.hDiv.{0, 0, 0}
                            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (6 : Real) (HMul.hMul.{0, 0, 0} C M)) s)
                            (HPow.hPow.{0, 0, 0} (Real.log ↑A) (3 : Nat))) := by sorry
