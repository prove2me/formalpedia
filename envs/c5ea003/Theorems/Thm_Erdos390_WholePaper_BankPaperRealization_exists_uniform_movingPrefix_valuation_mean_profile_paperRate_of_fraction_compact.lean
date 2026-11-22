-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_uniform_movingPrefix_valuation_mean_profile_paperRate_of_fraction_compact
-- name    : Erdos390.WholePaper.BankPaperRealization.exists_uniform_movingPrefix_valuation_mean_profile_paperRate_of_fraction_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:11:03.473614+00:00
-- url     : https://prove2.me/theorems/201ef664-b326-4fe7-9d89-f36bb54c4384
-- title:
--   Moving prefixes have uniform sharp full-valuation profiles
-- statement:
--   Write $L_n=\log n$, $s_n=n/\log n$, $y_n=\lfloor n^{2/9}\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le y_n\}$. For a prime $p\in\mathcal P_{n,W}$ put $k_p=\lfloor\log_p(y_n^4)\rfloor$ and $V_n(p)=\sum_{j=1}^{k_p}M_n(p^j)$, where $M_n(D)$ is the paper Dickman divisibility main term. Fix a pattern $P$, $0<A<C$, $r_{\min}>0$, and $W>1$ containing all its head primes. There exist $C_v>0,N_0$ such that for $n\ge N_0$, every endpoint $\lfloor An\rfloor<k\le\lfloor Cn\rfloor$ with physical prefix fraction at least $r_{\min}$, and every $p\in\mathcal P_{n,W}$, the prefix structured cell $S$ is nonempty and
--   $$|\mathbb E_{\mathrm{Unif}(S)}v_p(m)-V_n(p)|\le C_v/(pL_n).$$
--   This uses the same truncated Dickman main term as a fixed cell, uniformly over the moving upper endpoint. The physical prefix fraction means exactly $(k/n-A)/(C-A)$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosureMoving.lean#L434-L637

import Definitions.Def_erdos390_remaining_analytic_propositions_007

theorem Erdos390.WholePaper.BankPaperRealization.exists_uniform_movingPrefix_valuation_mean_profile_paperRate_of_fraction_compact : Erdos390.RemainingAnalyticGoal007_009 := by sorry
