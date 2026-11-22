-- Prove2me | Theorems.Thm_Erdos390_WholePaper_roughSaiasBaseFreeFractionalIntegral_hyperbola_sum_abs_succ_sub_le_two_inv_log_compact
-- name    : Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral_hyperbola_sum_abs_succ_sub_le_two_inv_log_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:46:05.789507+00:00
-- url     : https://prove2.me/theorems/f59fa0c1-f528-4e86-accf-064ce5bb2ad4
-- title:
--   Total variation of the fractional correction along a natural hyperbola
-- statement:
--   Let $2\le a\le b\le X$ be natural numbers with $\log X/\log a\le5$, and set $q_m=\lfloor X/m\rfloor$. Write $K(q,m,t)=D_\rho((\log q-\log t)/\log m)/\log m$ for the scaled Dickman kernel, where $D_\rho$ is the source-defined Dickman derivative, and $I(q,m)=\int_1^{m^5}\{t\}t^{-2}K(q,m,t)\,dt$ for its base-free fractional correction.
--
--   Then
--   $$\sum_{m=a}^{b-1}|I(q_{m+1},m+1)-I(q_m,m)|\le\frac2{\log a}.$$
--
--   The bound controls the smooth fractional component in weighted hyperbola summation.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughSaiasSharpVariation.lean#L1108-L1257

import Definitions.Def_erdos390_remaining_analytic_propositions_008

theorem Erdos390.WholePaper.roughSaiasBaseFreeFractionalIntegral_hyperbola_sum_abs_succ_sub_le_two_inv_log_compact : Erdos390.RemainingAnalyticGoal008_024 := by sorry
