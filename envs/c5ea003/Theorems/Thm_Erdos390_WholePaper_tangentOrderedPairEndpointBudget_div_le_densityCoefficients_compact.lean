-- Prove2me | Theorems.Thm_Erdos390_WholePaper_tangentOrderedPairEndpointBudget_div_le_densityCoefficients_compact
-- name    : Erdos390.WholePaper.tangentOrderedPairEndpointBudget_div_le_densityCoefficients_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:51:30.640377+00:00
-- url     : https://prove2.me/theorems/2ba4f7e4-2f37-4b92-bd8b-fac8df2abf86
-- title:
--   Endpoint collision budget from effective list density
-- statement:
--   Let $n>0$, $K,h,H\in\mathbb N$ and $d>0$. Each request $r$ has distinct prime endpoint labels $s_r,t_r\le H$ and a positive natural lower-cardinality bound $m_r$. Assume $H\le n$, $H^2\le n$, and $dn\le m_r a$ for each endpoint $a$ of $r$. If $N$ is the source's broad upper endpoint at $(n,K,h)$ and $P_N$ is its ordered-pair endpoint budget, then
--   $$\frac{P_N(r,u)}{m_rm_u}\le\frac{12}{d^2n}+\frac{3s_r}{d^2n}\mathbf1_{s_r\in\{s_u,t_u\}}+\frac{3t_r}{d^2n}\mathbf1_{t_r\in\{s_u,t_u\}}.$$
--   This gives explicit disjoint-label and shared-label coefficients for collision control.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/TangentPairArithmetic.lean#L432-L550

import Definitions.Def_erdos390_remaining_analytic_propositions_008

universe u_1

theorem Erdos390.WholePaper.tangentOrderedPairEndpointBudget_div_le_densityCoefficients_compact : Erdos390.RemainingAnalyticGoal008_039.{u_1} := by sorry
