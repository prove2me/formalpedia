-- Prove2me | Theorems.Thm_Erdos390_WholePaper_eventually_bankPaperCanonicalSectionNineBudgetClosure_compact
-- name    : Erdos390.WholePaper.eventually_bankPaperCanonicalSectionNineBudgetClosure_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:31:02.036883+00:00
-- url     : https://prove2.me/theorems/d29e2250-0367-432d-86cf-ecbaf7db52cd
-- title:
--   Eventual closure of the section-nine clean-list and budget estimates
-- statement:
--   Write $L=\log n$, $Y_n=\lfloor n^{2/9}\rfloor$, $h=\lceil cn/\log n\rceil$, and $K=K_0+1$. Fix a regular mesh $M$ with $\delta>0$, finite head set, bridge family $B_n$, and natural $W,K_0,d$. Assume $c>0$, $1<r_0<3/2$, $0<\delta_*<1/18$, $80C_{\rm Selberg}\delta_*<g(W,r_0)$, $W\ge2$, $2d+1\le W$, $\rho>1$, and $\rho^3<r_0$. Fix $T,\sigma>0$, $C_{\rm post}\ge0$, and $C_q\in\mathbb R$ with $(2/9)C_{\rm post}C_q\le T$. Require the mesh width to be at most the source paper-width choice for density $d_0=d(W,r_0)$ and parameters $\sigma,\rho,T$. Suppose eventually $B_n$ has size n and cutoff W, and active mass $q_n\le C_qn/\log n$. Then eventually, uniformly in compatible bank realizations, anchor certificates at depth d, scale-separation data, and endpoint functions, all split requests have positive lower-cardinality bound $\ell$, actual clean-list cardinality at least $\ell$, and $d_0n\le\ell$ times either endpoint label. In addition,
--
--   $$\mathcal B_{\rm main}\le d_0^2/48,\quad\mathcal B_{\rm error}\le d_0^2/96,\quad\mathcal B_{\rm ceil}\le d_0^2/96,$$
--
--   $$C_{\rm post}q_n/B_n.L\le T\frac{n/\log n}{\log(n^{2/9})},\qquad B_n.L\,(n/\log n)=n.$$
--
--   Here g, d, the width choice, and the three budgets are the source canonical distributed-tangent quantities.
--
--   The only external asymptotic mass input is the bound on the actual active mass; the clean lists and budgets are derived uniformly.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSectionNineBudgetClosure.lean#L222-L374

import Definitions.Def_erdos390_remaining_analytic_propositions_008

universe u_1

theorem Erdos390.WholePaper.eventually_bankPaperCanonicalSectionNineBudgetClosure_compact : Erdos390.RemainingAnalyticGoal008_005.{u_1} := by sorry
