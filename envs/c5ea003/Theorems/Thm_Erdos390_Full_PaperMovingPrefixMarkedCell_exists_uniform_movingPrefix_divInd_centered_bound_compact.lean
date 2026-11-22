-- Prove2me | Theorems.Thm_Erdos390_Full_PaperMovingPrefixMarkedCell_exists_uniform_movingPrefix_divInd_centered_bound_compact
-- name    : Erdos390.Full.PaperMovingPrefixMarkedCell.exists_uniform_movingPrefix_divInd_centered_bound_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:10:04.425314+00:00
-- url     : https://prove2.me/theorems/77b37b72-ee0f-4900-bb09-111481b54978
-- title:
--   Centered divisibility-prefix bound on a raw structured cell
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. For a head pattern $P$, let $S_P(A,C;n)$ be the positive $Y_n$-smooth integers in $(\lfloor An\rfloor,\lfloor Cn\rfloor]$ having exactly the valuations prescribed by $P$. Fix a pattern $P$ and $0<A<C$. Uniformly for integers $k,d$ with $\lfloor An\rfloor<k\le\lfloor Cn\rfloor$, $0<d\le Y_n^4$, all prime factors of $d$ at most $Y_n$, and $\gcd(d,\operatorname{modulus}(P))=1$, there exist $K>0,N_0$ such that for $n\ge N_0$, writing $\mathbb E_S$ for the source uniform average on $S=S_P(A,C;n)$,
--
--   $$\left|\mathbb E_S[\mathbf1_{d\mid m}\mathbf1_{m\le k}]-\mathbb E_S[\mathbf1_{d\mid m}]\mathbb E_S[\mathbf1_{m\le k}]\right|\le\frac K{dL_n}.$$
--
--   The centered estimate preserves the marked modulus factor needed when summing prime-power contributions.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperMovingPrefixMarkedCell.lean#L694-L849

import Definitions.Def_erdos390_remaining_analytic_propositions_004

theorem Erdos390.Full.PaperMovingPrefixMarkedCell.exists_uniform_movingPrefix_divInd_centered_bound_compact : Erdos390.RemainingAnalyticGoal004_005 := by sorry
