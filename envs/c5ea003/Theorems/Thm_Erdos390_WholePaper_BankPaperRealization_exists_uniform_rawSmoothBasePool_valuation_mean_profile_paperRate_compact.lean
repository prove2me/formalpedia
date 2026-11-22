-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_uniform_rawSmoothBasePool_valuation_mean_profile_paperRate_compact
-- name    : Erdos390.WholePaper.BankPaperRealization.exists_uniform_rawSmoothBasePool_valuation_mean_profile_paperRate_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:28:37.532648+00:00
-- url     : https://prove2.me/theorems/005d738e-2979-40b5-ac83-5c801259bdad
-- title:
--   The raw smooth base pool inherits the moving-prefix valuation profile
-- statement:
--   Write $L_n=\log n$, $s_n=n/\log n$, $y_n=\lfloor n^{2/9}\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le y_n\}$. For a prime $p\in\mathcal P_{n,W}$ put $k_p=\lfloor\log_p(y_n^4)\rfloor$ and $V_n(p)=\sum_{j=1}^{k_p}M_n(p^j)$, where $M_n(D)$ is the paper Dickman divisibility main term. Fix $W>1$, natural $K$, and $c>0$. There are $C_v>0,N_0$ such that for every $n\ge N_0$ and $p\in\mathcal P_{n,W}$, the canonical raw smooth-base pool $S$ for width $W$, multiplicity $K$, and upper-tail length associated to $c$ is nonempty and
--   $$|\mathbb E_{\mathrm{Unif}(S)}v_p(m)-V_n(p)|\le C_v/(pL_n).$$
--   This is the label-one, head-free broad pool used by the smooth source construction.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosureBroad.lean#L75-L177

import Definitions.Def_erdos390_remaining_analytic_propositions_007

theorem Erdos390.WholePaper.BankPaperRealization.exists_uniform_rawSmoothBasePool_valuation_mean_profile_paperRate_compact : Erdos390.RemainingAnalyticGoal007_010 := by sorry
