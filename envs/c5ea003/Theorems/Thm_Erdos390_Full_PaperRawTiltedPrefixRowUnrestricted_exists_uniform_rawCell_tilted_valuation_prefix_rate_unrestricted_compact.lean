-- Prove2me | Theorems.Thm_Erdos390_Full_PaperRawTiltedPrefixRowUnrestricted_exists_uniform_rawCell_tilted_valuation_prefix_rate_unrestricted_compact
-- name    : Erdos390.Full.PaperRawTiltedPrefixRowUnrestricted.exists_uniform_rawCell_tilted_valuation_prefix_rate_unrestricted_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:12:44.007496+00:00
-- url     : https://prove2.me/theorems/3557a911-c210-47b1-b71b-2f6bc068ad34
-- title:
--   Tilted raw valuation-prefix rate for an arbitrary fixed coefficient box
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. For a head pattern $P$, let $S_P(A,C;n)$ be the positive $Y_n$-smooth integers in $(\lfloor An\rfloor,\lfloor Cn\rfloor]$ having exactly the valuations prescribed by $P$. For coefficients $\eta$, the tilted cell law assigns mass proportional to $\exp(L_n^{-1}\sum_{q\in\mathcal P_{n,W}}\eta_q v_q(m))$. Fix $H$, $0<A<C$ with $C>0$, $B\ge0$, and $W>1$ containing the head primes. There are $\epsilon_n$ and $N_0$ with $\epsilon_n\log L_n\to0$ such that for $n\ge N_0$, all $\lfloor An\rfloor<k\le\lfloor Cn\rfloor$, $p\in\mathcal P_{n,W}$, and band coefficients $|\eta_q|\le B$, every nonempty cell has
--
--   $$|\operatorname{Cov}_{\mu^\eta}(v_p,\mathbf1_{m\le k})|\le\epsilon_n/p.$$
--
--   This supplies the raw moving-prefix terminal estimate without a smallness condition linking the coefficient box to the cutoff.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperRawTiltedPrefixRowUnrestricted.lean#L28-L349

import Definitions.Def_erdos390_remaining_analytic_propositions_004

theorem Erdos390.Full.PaperRawTiltedPrefixRowUnrestricted.exists_uniform_rawCell_tilted_valuation_prefix_rate_unrestricted_compact : Erdos390.RemainingAnalyticGoal004_007 := by sorry
