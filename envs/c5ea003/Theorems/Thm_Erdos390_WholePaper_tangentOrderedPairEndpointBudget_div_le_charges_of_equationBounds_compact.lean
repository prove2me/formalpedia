-- Prove2me | Theorems.Thm_Erdos390_WholePaper_tangentOrderedPairEndpointBudget_div_le_charges_of_equationBounds_compact
-- name    : Erdos390.WholePaper.tangentOrderedPairEndpointBudget_div_le_charges_of_equationBounds_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:51:10.638708+00:00
-- url     : https://prove2.me/theorems/fe26a5fe-9613-40d3-913f-02062fc68a17
-- title:
--   Assembly of four endpoint-equation charges
-- statement:
--   Let requests have two distinct natural endpoint labels $s_r,t_r$ and a natural lower-cardinality bound $m_r$. Fix $N\in\mathbb N$, $D\in\mathbb R$ and charges $H:\mathbb N\to\mathbb R$. Assume every pair of endpoint choices $a\in\{s_r,t_r\}$, $b\in\{s_u,t_u\}$ satisfies $E_N(a,b)/(m_rm_u)\le D/4+\mathbf1_{a=b}H(a)$, where $E_N$ is the source's endpoint-equation budget. Let $P_N(r,u)$ be the sum of these four budgets. Then
--   $$\frac{P_N(r,u)}{m_rm_u}\le D+\mathbf1_{s_r\in\{s_u,t_u\}}H(s_r)+\mathbf1_{t_r\in\{s_u,t_u\}}H(t_r).$$
--   No positivity of the $m_r$ is required in this statement; division follows the real-field convention at zero. This collects disjoint and shared-label costs for collision estimates.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/TangentPairArithmetic.lean#L124-L251

import Definitions.Def_erdos390_remaining_analytic_propositions_008

universe u_1

theorem Erdos390.WholePaper.tangentOrderedPairEndpointBudget_div_le_charges_of_equationBounds_compact : Erdos390.RemainingAnalyticGoal008_038.{u_1} := by sorry
