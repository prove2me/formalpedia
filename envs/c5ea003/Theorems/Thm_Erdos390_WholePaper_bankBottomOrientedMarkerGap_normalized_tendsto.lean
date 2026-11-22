-- Prove2me | Theorems.Thm_Erdos390_WholePaper_bankBottomOrientedMarkerGap_normalized_tendsto
-- name    : Erdos390.WholePaper.bankBottomOrientedMarkerGap_normalized_tendsto
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:01:14.327966+00:00
-- url     : https://prove2.me/theorems/d7cdabf8-2ed4-4661-83c2-4662947329c5
-- title:
--   Asymptotic width of an oriented bottom-marker pool
-- statement:
--   Let $c>0$ and let $\pi$ be any bottom orientation pool. Set $M_n$ to the upper endpoint determined by the tail length at $c$, and write $L_\pi(n,M_n),U_\pi(n,M_n)$ for the oriented marker endpoints. If $d_\pi$ is the underlying row's marker denominator and $s(n)=n/\log n$, then
--   $$\frac{U_\pi(n,M_n)-L_\pi(n,M_n)}{s(n)}\longrightarrow\frac{c}{2d_\pi}\qquad(n\to\infty).$$
--   The subtraction in the numerator is real subtraction of the natural endpoints. The result allocates half the row-scale marker width to each orientation.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankBottomMarkerPoolScale.lean#L405-L499

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006

theorem Erdos390.WholePaper.bankBottomOrientedMarkerGap_normalized_tendsto :
∀ {c : Real},
  LT.lt.{0} (0 : Real) c →
    ∀ (pool : Erdos390.WholePaper.BankBottomOrientationPool),
      Filter.Tendsto.{0, 0}
        (fun n =>
          HDiv.hDiv.{0, 0, 0}
            (HSub.hSub.{0, 0, 0}
              ↑(Erdos390.WholePaper.bankBottomOrientedMarkerUpper n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) pool)
              ↑(Erdos390.WholePaper.bankBottomOrientedMarkerLower n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) pool))
            (Erdos390.WholePaper.secondOrderScale n))
        Filter.atTop.{0} (nhds.{0} (Erdos390.WholePaper.bankBottomOrientedPrimeConstant c pool)) := by sorry
