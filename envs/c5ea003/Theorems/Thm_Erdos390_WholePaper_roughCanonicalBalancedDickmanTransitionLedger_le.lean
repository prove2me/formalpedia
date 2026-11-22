-- Prove2me | Theorems.Thm_Erdos390_WholePaper_roughCanonicalBalancedDickmanTransitionLedger_le
-- name    : Erdos390.WholePaper.roughCanonicalBalancedDickmanTransitionLedger_le
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:54:18.257635+00:00
-- url     : https://prove2.me/theorems/1142b29a-37d4-467a-a67b-04420af60a80
-- title:
--   Balanced Dickman transition ledger at the canonical row scale
-- statement:
--   Write $L=\log n$, $Y_n=\lfloor n^{2/9}\rfloor$, $h=\lceil cn/\log n\rceil$, and $K=K_0+1$. Fix natural W and $K_0$, real $\beta$, and $c>0$. Let $n\ge2$, $0<r\le n$, $y\ge2$, $L\ge1$, $\log y\ge L/5$, $h\le2cn/L$, and $Kh\le n$. Put $x=\lfloor n/r\rfloor$, use the source head density and balanced alpha, and take the four physical endpoints $\lfloor(2n+h)/r\rfloor$, $\lfloor2n/r\rfloor$, $\lfloor(2n-Kh)/r\rfloor$, and x. Assume additionally $h>0$. The source physical Dickman transition ledger $\mathcal D$ at these parameters satisfies
--
--   $$\mathcal D\le C_{\rm main}(W,K_0,c,\beta)(x/L^2+1),$$
--
--   where $C_{\rm main}$ is the sharp main-row scale constant.
--
--   The constant is fixed before n and the row label are chosen.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughSaiasSharpCanonicalRowPaperScale.lean#L730-L1071

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_009

theorem Erdos390.WholePaper.roughCanonicalBalancedDickmanTransitionLedger_le : Erdos390.RemainingAnalyticGoal008_014 := by sorry
