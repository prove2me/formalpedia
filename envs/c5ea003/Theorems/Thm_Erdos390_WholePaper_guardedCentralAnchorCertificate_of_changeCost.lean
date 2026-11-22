-- Prove2me | Theorems.Thm_Erdos390_WholePaper_guardedCentralAnchorCertificate_of_changeCost
-- name    : Erdos390.WholePaper.guardedCentralAnchorCertificate_of_changeCost
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:23:08.889117+00:00
-- url     : https://prove2.me/theorems/23d95fd6-0365-47d4-a66f-f90555c272c0
-- title:
--   Guarded central anchors from a finite modification budget
-- statement:
--   Let $c>C_0$, $R\ge1$, and $n$ exceed the central-anchor cutoff threshold for $R$. Suppose a central-anchor certificate is given. Let $S$ be a finite subset of its large central primes, all at most $n$, and let $\ell,r:\mathbb N\to\mathbb N$ specify forbidden cofactors. For each $p\in S$ with $\lfloor n/p\rfloor=1$, require $\ell(p)\ne3$ and $r(p)\ne3$. If, for every prime $p\le2R+1$,
--   $$|S|\lfloor\log_2(2R+1)\rfloor\le\frac{c-C_0}{6(p-1)}\frac n{\log n},$$
--   then a guarded central-anchor certificate exists for these forbidden cofactors and this changed set.
--
--   The certificate concerns the newly modified cofactor function and retains the exact anchor product, interval support, divisibility and collision-avoidance conditions.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/CentralAnchorGuardedCertificate.lean#L54-L196

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007

theorem Erdos390.WholePaper.guardedCentralAnchorCertificate_of_changeCost :
∀ {c : Real} {R n : Nat} {left right : Nat → Nat} {changed : Finset.{0} Nat},
  LT.lt.{0} Erdos390.WholePaper.C0 c →
    LE.le.{0} (1 : Nat) R →
      LE.le.{0} (Erdos390.WholePaper.centralAnchorCutoffThreshold R) n →
        ∀ (certificate : Erdos390.WholePaper.CentralAnchorCertificate c R n),
          HasSubset.Subset.{0} changed
              (Erdos390.WholePaper.largeCentralPrimes n (Erdos390.WholePaper.centralAnchorCutoff R n)) →
            (∀ (p : Nat), Membership.mem.{0, 0} changed p → LE.le.{0} p n) →
              (∀ (p : Nat),
                  Membership.mem.{0, 0} changed p →
                    Eq.{1} (HDiv.hDiv.{0, 0, 0} n p) (1 : Nat) →
                      And (Ne.{1} (3 : Nat) (left p)) (Ne.{1} (3 : Nat) (right p))) →
                (∀ (ℓ : Nat),
                    Membership.mem.{0, 0}
                        (Erdos390.WholePaper.primesUpTo
                          (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) R) (1 : Nat)))
                        ℓ →
                      LE.le.{0}
                        (↑(HMul.hMul.{0, 0, 0} (Finset.card.{0} changed)
                            (Nat.log (2 : Nat) (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) R) (1 : Nat)))))
                        (HMul.hMul.{0, 0, 0}
                          (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} c Erdos390.WholePaper.C0)
                            (HMul.hMul.{0, 0, 0} (6 : Real) ↑(HSub.hSub.{0, 0, 0} ℓ (1 : Nat))))
                          (Erdos390.WholePaper.secondOrderScale n))) →
                  Nonempty.{1} (Erdos390.WholePaper.GuardedCentralAnchorCertificate c R n left right changed) := by sorry
