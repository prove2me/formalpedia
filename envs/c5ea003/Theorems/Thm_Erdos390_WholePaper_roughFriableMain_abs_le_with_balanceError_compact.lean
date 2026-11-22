-- Prove2me | Theorems.Thm_Erdos390_WholePaper_roughFriableMain_abs_le_with_balanceError_compact
-- name    : Erdos390.WholePaper.roughFriableMain_abs_le_with_balanceError_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:46:22.285129+00:00
-- url     : https://prove2.me/theorems/ab165fa6-5ffb-4c43-9dbb-04cff434c09f
-- title:
--   Balanced Dickman sums with an explicit imbalance error
-- statement:
--   Let $I$ be a finite index set, $c_i\in\mathbb R$, and $X_i,b,y\in\mathbb N$. Put $u(X,y)=\log X/\log y$. Suppose $u(X_i,y)\le5$ for all $i\in I$ and $0\le u(b,y)\le5$. Then
--   $$\left|\sum_{i\in I}c_iX_i\rho(u(X_i,y))\right|\le\sum_{i\in I}|c_i|X_i|u(X_i,y)-u(b,y)|+\left|\sum_{i\in I}c_iX_i\right|.$$
--   This isolates a balance defect from the local variation of the Dickman factor.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughBalancedFriableResidualReduction.lean#L257-L358

import Definitions.Def_erdos390_remaining_analytic_propositions_008

universe u_1

theorem Erdos390.WholePaper.roughFriableMain_abs_le_with_balanceError_compact : Erdos390.RemainingAnalyticGoal008_022.{u_1} := by sorry
