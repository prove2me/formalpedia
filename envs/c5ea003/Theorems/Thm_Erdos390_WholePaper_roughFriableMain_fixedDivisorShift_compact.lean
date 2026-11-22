-- Prove2me | Theorems.Thm_Erdos390_WholePaper_roughFriableMain_fixedDivisorShift_compact
-- name    : Erdos390.WholePaper.roughFriableMain_fixedDivisorShift_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:46:12.643548+00:00
-- url     : https://prove2.me/theorems/c1742183-23f0-45aa-9199-de2480841351
-- title:
--   Fixed-divisor shift of the Dickman main term
-- statement:
--   Let $X,y,d$ be natural numbers with $y\ge2$, $0<d\le X$, and $\log X\le5\log y$. Write $u(X,y)=\log X/\log y$ and let $\rho$ be the Dickman function. Then
--   $$\left|\lfloor X/d\rfloor\rho(u(\lfloor X/d\rfloor,y))-\frac{X\rho(u(X,y))}{d}\right|\le3+\frac{X\log d}{d\log y}.$$
--   This quantifies both the floor loss and the change of the Dickman parameter caused by a fixed divisor.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughFixedHeadFriableShift.lean#L131-L239

import Definitions.Def_erdos390_remaining_analytic_propositions_008

theorem Erdos390.WholePaper.roughFriableMain_fixedDivisorShift_compact : Erdos390.RemainingAnalyticGoal008_023 := by sorry
