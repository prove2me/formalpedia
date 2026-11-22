-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_uniform_rawStructuredCell_valuation_mean_profile_paperRate
-- name    : Erdos390.WholePaper.BankPaperRealization.exists_uniform_rawStructuredCell_valuation_mean_profile_paperRate
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:53:51.662608+00:00
-- url     : https://prove2.me/theorems/0127f20e-49bf-4ee2-ad87-8e1b0eb88757
-- title:
--   A fixed raw structured cell has the sharp full-valuation profile
-- statement:
--   Write $L_n=\log n$, $s_n=n/\log n$, $y_n=\lfloor n^{2/9}\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le y_n\}$. For a prime $p\in\mathcal P_{n,W}$ put $k_p=\lfloor\log_p(y_n^4)\rfloor$ and $V_n(p)=\sum_{j=1}^{k_p}M_n(p^j)$, where $M_n(D)$ is the paper Dickman divisibility main term. Fix a head pattern $P$, real $0<A<C$, and $W>1$ containing all head primes. There exist $C_v>0,N_0$ such that for every $n\ge N_0$ and $p\in\mathcal P_{n,W}$, the structured cell $S=\operatorname{structuredCell}(P,\lfloor An\rfloor,\lfloor Cn\rfloor,y_n)$ is nonempty and
--   $$|\mathbb E_{\mathrm{Unif}(S)}v_p(m)-V_n(p)|\le\frac{C_v}{pL_n}.$$
--   Nonemptiness is part of the conclusion, and the estimate concerns the genuine full valuation.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosure.lean#L61-L260

import Definitions.Def_erdos390_remaining_analytic_propositions_007
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004

theorem Erdos390.WholePaper.BankPaperRealization.exists_uniform_rawStructuredCell_valuation_mean_profile_paperRate : Erdos390.RemainingAnalyticGoal007_011 := by sorry
