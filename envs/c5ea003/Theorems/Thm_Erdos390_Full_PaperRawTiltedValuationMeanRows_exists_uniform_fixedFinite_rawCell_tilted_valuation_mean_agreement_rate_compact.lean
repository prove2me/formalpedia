-- Prove2me | Theorems.Thm_Erdos390_Full_PaperRawTiltedValuationMeanRows_exists_uniform_fixedFinite_rawCell_tilted_valuation_mean_agreement_rate_compact
-- name    : Erdos390.Full.PaperRawTiltedValuationMeanRows.exists_uniform_fixedFinite_rawCell_tilted_valuation_mean_agreement_rate_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:12:08.385982+00:00
-- url     : https://prove2.me/theorems/0d264423-5c62-4050-b919-6330a56221b3
-- title:
--   Uniform agreement of tilted valuation means across finitely many raw cells
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. For a head pattern $P$, let $S_P(A,C;n)$ be the positive $Y_n$-smooth integers in $(\lfloor An\rfloor,\lfloor Cn\rfloor]$ having exactly the valuations prescribed by $P$. For coefficients $\eta$, the tilted cell law assigns mass proportional to $\exp(L_n^{-1}\sum_{q\in\mathcal P_{n,W}}\eta_q v_q(m))$. Fix a finite cell index set, patterns $H_c$, and real endpoints $0<A_c<C_c\le C_{\max}$ with $C_c>0$. Fix $W>1$ containing every head prime, and any coefficient bound $B\ge0$. There are a nonnegative sequence $\epsilon_n$ and $N_0$ such that $\epsilon_n\log L_n\to0$ and, for $n\ge N_0$, all $p\in\mathcal P_{n,W}$, all $|\eta_q|\le B$ on this band, and all nonempty cells, their tilted laws $\mu_c^\eta$ satisfy
--
--   $$|\mathbb E_{\mu_c^\eta}v_p-\mathbb E_{\mu_{c\prime}^\eta}v_p|\le\epsilon_n/p\qquad\text{for every }c,c\prime.$$
--
--   The rate is uniform over the finite family and the full coefficient box, with no relation imposed between the box size and the cutoff.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperRawTiltedValuationMeanRows.lean#L110-L408

import Definitions.Def_erdos390_remaining_analytic_propositions_004

universe u_1

theorem Erdos390.Full.PaperRawTiltedValuationMeanRows.exists_uniform_fixedFinite_rawCell_tilted_valuation_mean_agreement_rate_compact : Erdos390.RemainingAnalyticGoal004_008.{u_1} := by sorry
