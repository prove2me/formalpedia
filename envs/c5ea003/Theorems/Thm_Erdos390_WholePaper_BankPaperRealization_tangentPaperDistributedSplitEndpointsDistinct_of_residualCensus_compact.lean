-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_tangentPaperDistributedSplitEndpointsDistinct_of_residualCensus_compact
-- name    : Erdos390.WholePaper.BankPaperRealization.tangentPaperDistributedSplitEndpointsDistinct_of_residualCensus_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:10:16.066176+00:00
-- url     : https://prove2.me/theorems/fce1aa98-a5c2-4df7-94ee-05099a0e629e
-- title:
--   Collision-free distributed tangent realization from residual ledgers
-- statement:
--   Let $V$ be finite, with an injective prime labeling $p:V\to\mathbb N$, and let $F\ge0$ be a flow whose positive edges have distinct endpoints. Suppose its divergence is a residual vector $r$, its total traffic is at most the distributed residual/cut ledger, and the incident flow at $p_v$ is at most $|r_v|+2b_v$, where $b$ is the port-load vector. Assume $p_v|r_v|\le R_*$ and $p_vb_v\le B_*$, and $p_v\le H$ with $H\le n$, $H^2\le n$, $n>0$. Fix a paper bank, a compatible guarded central-anchor certificate, a finite exceptional set, and natural list parameters $K,h,P_{\rm head},X_0$.
--
--   Take $L,\sigma,N,d>0$ with $LN=n$. Suppose the total ledger is at most $C_T C_\tau Nw+e_TN$, and $R_*+2B_*\le C_I C_\tau Nw+e_IN$. The source's distributed main, error and ceiling budgets for these constants are required to be at most $d^2/48,d^2/96,d^2/96$, respectively. Every split request must have a positive lower-cardinality bound $m_q$ no greater than its clean multiplier-list size, and must satisfy $dn\le m_q a$ at either endpoint label $a$.
--
--   Then one can choose a multiplier $z_q$ from each clean list so that all selected endpoint products are distinct. Moreover, divergence is $r$, and for every natural prime-index $\ell$,
--   $$\sum_q w_q\bigl(v_\ell(s_q)-v_\ell(t_q)\bigr)=\sum_{v\in V}r_vv_\ell(p_v).$$
--   Here $q$ ranges over the split positive-flow requests, $w_q$ is its split weight, and $s_q,t_q$ its labels; $v_\ell$ denotes the natural factorization coordinate, defined also for nonprime $\ell$. This turns explicit residual, traffic, density and parameter budgets into a collision-free realization.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/TangentDistributedFlowCensus.lean#L1143-L1371

import Definitions.Def_erdos390_remaining_analytic_propositions_008

universe u_1

theorem Erdos390.WholePaper.BankPaperRealization.tangentPaperDistributedSplitEndpointsDistinct_of_residualCensus_compact : Erdos390.RemainingAnalyticGoal008_001.{u_1} := by sorry
