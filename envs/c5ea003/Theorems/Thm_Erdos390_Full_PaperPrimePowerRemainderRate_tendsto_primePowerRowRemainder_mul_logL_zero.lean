-- Prove2me | Theorems.Thm_Erdos390_Full_PaperPrimePowerRemainderRate_tendsto_primePowerRowRemainder_mul_logL_zero
-- name    : Erdos390.Full.PaperPrimePowerRemainderRate.tendsto_primePowerRowRemainder_mul_logL_zero
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:28:59.817419+00:00
-- url     : https://prove2.me/theorems/575d9454-cdbe-4edd-ac16-08281620fb5a
-- title:
--   The aggregated prime-power row retains one logarithmic decay rate
-- statement:
--   Let $L_n=\log n$, $W>1$, $G_0,B,G_f\ge0$, and $\epsilon_n\ge0$. Suppose $\epsilon_n$, $\epsilon_n\log L_n$, and $\epsilon_n(\log L_n)^2$ all tend to zero. Let $R_n$ be the common chamber remainder with coefficient scale $(2B/L_n)e^{2B/\log W}$; let $A_{\rm agg}$ be the finite prime-power aggregation constant, $S_n=\sum_{p\in\mathcal P_{n,W}}1/p$, and $T_n$ the source's outside-chamber tail-row majorant with parameters $G_f,W$. For the exact row remainder
--   $$Q_n=A_{\rm agg}R_n(S_n+5)/W+T_n,$$
--   one has $Q_n\log L_n\to0$. Here $\mathcal P_{n,W}$ is the moving prime band. This is the decay required by the moving-low sharp-row transfer. The moving prime band is $\{p\text{ prime}:W<p\le\lfloor n^{2/9}\rfloor\}$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperPrimePowerRemainderRate.lean#L440-L550

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_004

theorem Erdos390.Full.PaperPrimePowerRemainderRate.tendsto_primePowerRowRemainder_mul_logL_zero :
∀ (epsilon : Nat → Real) (G₀ B Gf : Real) (W : Nat),
  Filter.Tendsto.{0, 0} epsilon Filter.atTop.{0} (nhds.{0} (0 : Real)) →
    Filter.Tendsto.{0, 0} (fun n => HMul.hMul.{0, 0, 0} (epsilon n) (Real.log (Erdos390.Full.Scale.L n)))
        Filter.atTop.{0} (nhds.{0} (0 : Real)) →
      Filter.Tendsto.{0, 0}
          (fun n =>
            HMul.hMul.{0, 0, 0} (epsilon n) (HPow.hPow.{0, 0, 0} (Real.log (Erdos390.Full.Scale.L n)) (2 : Nat)))
          Filter.atTop.{0} (nhds.{0} (0 : Real)) →
        (∀ (n : Nat), LE.le.{0} (0 : Real) (epsilon n)) →
          LE.le.{0} (0 : Real) G₀ →
            LE.le.{0} (0 : Real) B →
              LE.le.{0} (0 : Real) Gf →
                LT.lt.{0} (1 : Nat) W →
                  Filter.Tendsto.{0, 0}
                    (fun n =>
                      HMul.hMul.{0, 0, 0}
                        (Erdos390.Full.PaperPrimePowerRemainderRate.primePowerRowRemainder epsilon G₀ B Gf W n)
                        (Real.log (Erdos390.Full.Scale.L n)))
                    Filter.atTop.{0} (nhds.{0} (0 : Real)) := by sorry
