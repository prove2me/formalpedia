-- Prove2me | Theorems.Thm_Erdos390_WholePaper_roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log_of_cutoff_compact
-- name    : Erdos390.WholePaper.roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log_of_cutoff_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:49:06.909444+00:00
-- url     : https://prove2.me/theorems/58d0ef62-c7a0-46f4-ad85-5b3ed26ba52a
-- title:
--   Kernel variation along a hyperbola with one cutoff
-- statement:
--   Let $2\le a\le c\le b\le X$ be natural numbers and $t>0$. Set $q_m=\lfloor X/m\rfloor$ and let $K$ be the scaled Dickman kernel. Suppose $t\le q_m/m$ and $(\log q_m-\log t)/\log m\le5$ for $a\le m\le c$, while $q_m/m<t$ for $c<m\le b$. Then
--   $$\sum_{m=a}^{b-1}|K(q_{m+1},m+1,t)-K(q_m,m,t)|\le\frac2{\log a}.$$
--
--   This accounts explicitly for the single transition from the active kernel to zero.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughSaiasSharpVariation.lean#L638-L736

import Definitions.Def_erdos390_remaining_analytic_propositions_008

theorem Erdos390.WholePaper.roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log_of_cutoff_compact : Erdos390.RemainingAnalyticGoal008_032 := by sorry
