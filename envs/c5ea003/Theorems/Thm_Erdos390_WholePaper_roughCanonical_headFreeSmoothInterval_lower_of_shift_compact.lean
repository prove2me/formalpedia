-- Prove2me | Theorems.Thm_Erdos390_WholePaper_roughCanonical_headFreeSmoothInterval_lower_of_shift_compact
-- name    : Erdos390.WholePaper.roughCanonical_headFreeSmoothInterval_lower_of_shift_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:10:17.131297+00:00
-- url     : https://prove2.me/theorems/03f787ec-e7de-42be-9f41-f1f38f2bef5e
-- title:
--   Head-free smooth interval lower bound from divisor shifts
-- statement:
--   Fix $W$, $K>0$, and a natural threshold $Y_0$. Let $P_W$ and $d_W$ denote the rough-head modulus and density. Assume that for every $z\ge Y_0$, positive divisor $d\mid P_W$, $d\le X$ and $\log X\le5\log z$,
--   $$|\Psi(\lfloor X/d\rfloor,z)-\Psi(X,z)/d|\le KX/(d\log z)+3.$$
--   For natural endpoints with $Y_0\le y$, $W\le y$, $y\ge2$, $P_W\le A\le B$ and $\log B\le5\log y$, let $S(A,B;y)$ be the smooth interval and $S_W^*(A,B;y)$ its head-free subset. Then
--   $$|S_W^*(A,B;y)|\ge d_W|S(A,B;y)|-P_W\left(\frac{K(A+B)}{\log y}+6\right).$$
--   This makes the loss in the finite Möbius removal of head primes explicit.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalRawBroadSurplusAsymptotic.lean#L365-L472

import Definitions.Def_erdos390_remaining_analytic_propositions_008

theorem Erdos390.WholePaper.roughCanonical_headFreeSmoothInterval_lower_of_shift_compact : Erdos390.RemainingAnalyticGoal008_018 := by sorry
