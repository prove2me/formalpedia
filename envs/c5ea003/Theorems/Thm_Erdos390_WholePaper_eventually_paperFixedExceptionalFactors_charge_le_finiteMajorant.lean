-- Prove2me | Theorems.Thm_Erdos390_WholePaper_eventually_paperFixedExceptionalFactors_charge_le_finiteMajorant
-- name    : Erdos390.WholePaper.eventually_paperFixedExceptionalFactors_charge_le_finiteMajorant
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:05:36.609403+00:00
-- url     : https://prove2.me/theorems/d63e8345-9b0c-44d9-8967-e23acb2e3e0d
-- title:
--   Low-prime charge of fixed exceptional factors
-- statement:
--   Fix $c>0$ and $\delta>0$. For all sufficiently large natural $n$, every bank realization $R$ on the canonical interval and every prime $p\le y(n)$ satisfy
--   $$v_p\!\left(\prod_{a\in G_{\rm fix}(R,\delta)}a\right)\le M_{\rm exc}(c,\delta,n,p),$$
--   where $G_{\rm fix}$ is the paper fixed exceptional factor set and $M_{\rm exc}$ is its canonical finite charge majorant.
--
--   This bounds the literal valuation charge without assuming a separate charge estimate.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperFixedExceptionalChargeAsymptotic.lean#L532-L818

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008

theorem Erdos390.WholePaper.eventually_paperFixedExceptionalFactors_charge_le_finiteMajorant :
∀ {c deltaStar : Real},
  LT.lt.{0} (0 : Real) c →
    LT.lt.{0} (0 : Real) deltaStar →
      ∀ᶠ (n : Nat) in Filter.atTop.{0},
        ∀
          (R :
            Erdos390.WholePaper.BankPaperRealization n
              (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)))
          (p : Nat),
          Nat.Prime p →
            LE.le.{0} p (Erdos390.Full.ArithmeticModel.yNat n) →
              LE.le.{0}
                (↑((Nat.factorization
                      (Finset.prod.{0, 0}
                        (Erdos390.WholePaper.BankPaperRealization.paperFixedExceptionalFactors R deltaStar) id.{1}))
                    p))
                (Erdos390.WholePaper.paperExceptionalFiniteChargeMajorant c deltaStar n p) := by sorry
