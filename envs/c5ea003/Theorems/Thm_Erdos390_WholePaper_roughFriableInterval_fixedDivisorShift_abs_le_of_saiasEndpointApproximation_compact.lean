-- Prove2me | Theorems.Thm_Erdos390_WholePaper_roughFriableInterval_fixedDivisorShift_abs_le_of_saiasEndpointApproximation_compact
-- name    : Erdos390.WholePaper.roughFriableInterval_fixedDivisorShift_abs_le_of_saiasEndpointApproximation_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:42:46.960031+00:00
-- url     : https://prove2.me/theorems/74ff7132-bce3-4635-a68c-c0727d143190
-- title:
--   Fixed-divisor interval shift from a Saias endpoint approximation
-- statement:
--   Assume the compact bounded-variation translation principle: for every function f of variation at most 2 on [−5,5] and a,b∈[0,5], the integral over v∈[0,5] of |f(a−v)−f(b−v)| is at most 2|a−b|. Let η be an endpoint error rate and Y₀ a threshold such that the source Saias endpoint error at (X,y) has magnitude at most η(y)X whenever y≥max(Y₀,2), X>0 and log X≤5 log y. Fix natural numbers y≥max(Y₀,2), 0<d≤A≤B, with log B≤5 log y. Write Ψ(X,y) for the count of y-friable positive integers at most X, A_d=⌊A/d⌋ and B_d=⌊B/d⌋. Define Pη(a,b;y)=η(y)(a+b)+5(b−a)/log y for ordered natural endpoints. Then the genuine friable interval shift satisfies the following cancellation-preserving bound; its right side is roughSaiasIntervalFixedDivisorShiftBudget.
--
--   $$\left|\Psi(B_d,y)-\Psi(A_d,y)-\frac{\Psi(B,y)-\Psi(A,y)}d\right|\le6+\frac{(B-A)(\log d+2)}{d\log y}+P_\eta(A_d,B_d;y)+\frac{P_\eta(A,B;y)}d.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughSaiasSharpFixedHeadIntervalShift.lean#L344-L457

import Definitions.Def_erdos390_remaining_analytic_propositions_008

theorem Erdos390.WholePaper.roughFriableInterval_fixedDivisorShift_abs_le_of_saiasEndpointApproximation_compact : Erdos390.RemainingAnalyticGoal008_021 := by sorry
