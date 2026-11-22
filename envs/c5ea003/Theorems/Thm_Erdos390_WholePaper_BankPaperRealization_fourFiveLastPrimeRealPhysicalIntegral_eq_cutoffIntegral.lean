-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_fourFiveLastPrimeRealPhysicalIntegral_eq_cutoffIntegral
-- name    : Erdos390.WholePaper.BankPaperRealization.fourFiveLastPrimeRealPhysicalIntegral_eq_cutoffIntegral
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:53:52.05039+00:00
-- url     : https://prove2.me/theorems/f94dc4aa-7335-4857-b4da-f976acdcd9d7
-- title:
--   The real last-prime integral is an exact common-domain cutoff integral
-- statement:
--   Let $m,y,A,B$ be natural numbers with $2\le y\le A\le B$, and let $q=(q_1,\ldots,q_m)$ be an indexed tuple of primes satisfying $y<q_i\le B$ for every $i$. Set $Q=\prod_iq_i>0$. The real last-prime physical integral satisfies
--   $$I_{\rm last}(q;y,A,B)=\frac1Q\int_A^B1_{\{Qy<t\}}\frac{dt}{\log(t/Q)}.$$
--   The integrand is defined to be zero when $t\le Qy$. Thus the moving last-prime domain is represented exactly on the fixed physical interval, with no endpoint rounding remainder.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperFourFiveRealCommonDomainIdentification.lean#L115-L223

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_009

theorem Erdos390.WholePaper.BankPaperRealization.fourFiveLastPrimeRealPhysicalIntegral_eq_cutoffIntegral :
∀ {m y A B : Nat} {q : Fin m → Nat},
  LE.le.{0} (2 : Nat) y →
    LE.le.{0} y A →
      LE.le.{0} A B →
        Membership.mem.{0, 0} (Erdos390.WholePaper.BankPaperRealization.fourFiveOrderedPrimePrefixSet m y B) q →
          Eq.{1} (Erdos390.WholePaper.BankPaperRealization.fourFiveLastPrimeRealPhysicalIntegral q y A B)
            (HMul.hMul.{0, 0, 0} (Inv.inv.{0} (Erdos390.WholePaper.BankPaperRealization.fourFiveRealPrefixProduct q))
              (∫ (t : Real) in ↑A..↑B,
                Erdos390.WholePaper.BankPaperRealization.fourFiveRealPrefixCutoffKernel
                  (Erdos390.WholePaper.BankPaperRealization.fourFiveRealPrefixProduct q) y t)) := by sorry
