-- Prove2me | Theorems.Thm_Erdos390_Full_PaperRawPrefixValuationRow_exists_uniform_rawCell_valuation_prefix_bound_compact
-- name    : Erdos390.Full.PaperRawPrefixValuationRow.exists_uniform_rawCell_valuation_prefix_bound_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:10:47.655101+00:00
-- url     : https://prove2.me/theorems/86184bd2-42d5-4588-96ce-abe957986b80
-- title:
--   Explicit raw valuation-prefix covariance bound
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. For a head pattern $P$, let $S_P(A,C;n)$ be the positive $Y_n$-smooth integers in $(\lfloor An\rfloor,\lfloor Cn\rfloor]$ having exactly the valuations prescribed by $P$. Fix $H$, $0<A<C$ with $C>0$, and $W>1$ containing every head prime. There exist $K,G>0$ and $N_0$ such that for $n\ge N_0$, $\lfloor An\rfloor<k\le\lfloor Cn\rfloor$, $p\in\mathcal P_{n,W}$, and any nonempty $S=S_H(A,C;n)$ with uniform law $\mu$,
--
--   $$|\operatorname{Cov}_{\mu}(v_p,\mathbf1_{m\le k})|\le\frac{2K}{pL_n}+\frac{4G(s_W L_n)^2}{p^2Y_n^2}.$$
--
--   Here $s_W$ is the source prime-power cutoff scale (`cutoffScale`).
--
--   The estimate exposes the beyond-four-prime-power tail separately from the principal reciprocal row bound.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperRawPrefixValuationRow.lean#L146-L370

import Definitions.Def_erdos390_remaining_analytic_propositions_004

theorem Erdos390.Full.PaperRawPrefixValuationRow.exists_uniform_rawCell_valuation_prefix_bound_compact : Erdos390.RemainingAnalyticGoal004_006 := by sorry
