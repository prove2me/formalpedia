-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_uniform_guardedSmoothBasePool_valuation_mean_profile_paperRate_compact
-- name    : Erdos390.WholePaper.BankPaperRealization.exists_uniform_guardedSmoothBasePool_valuation_mean_profile_paperRate_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:28:31.338534+00:00
-- url     : https://prove2.me/theorems/309390f6-f815-44f7-b26c-db1135ae5b50
-- title:
--   The guarded smooth broad pool retains the sharp valuation profile
-- statement:
--   Write $L_n=\log n$, $s_n=n/\log n$, $y_n=\lfloor n^{2/9}\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le y_n\}$. For a prime $p\in\mathcal P_{n,W}$ put $k_p=\lfloor\log_p(y_n^4)\rfloor$ and $V_n(p)=\sum_{j=1}^{k_p}M_n(p^j)$, where $M_n(D)$ is the paper Dickman divisibility main term. Fix $W>1$, natural multiplicity $K$ and depth $d$, and $c>0$. There exist $C_v>0$ and $N_0$ such that uniformly over every bank realization at $n\ge N_0$, its guarded central-anchor certificate at depth $d$, every real $\delta_*$, and every band prime $p$, the nonempty guarded broad correction pool of label one satisfies
--   $$\left|\mathbb E_{\mathrm{Unif}(\mathrm{guardedBroadPool}_1)}v_p(m)-V_n(p)\right|\le\frac{C_v}{pL_n}.$$
--   The constant is independent of the bank, certificate, and $\delta_*$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosureBroad.lean#L258-L566

import Definitions.Def_erdos390_remaining_analytic_propositions_007

theorem Erdos390.WholePaper.BankPaperRealization.exists_uniform_guardedSmoothBasePool_valuation_mean_profile_paperRate_compact : Erdos390.RemainingAnalyticGoal007_006 := by sorry
