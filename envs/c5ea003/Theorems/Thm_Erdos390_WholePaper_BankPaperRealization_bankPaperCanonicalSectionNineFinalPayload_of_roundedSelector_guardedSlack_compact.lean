-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack_compact
-- name    : Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:23:01.41363+00:00
-- url     : https://prove2.me/theorems/392dd029-0f9d-4c7d-8652-ac28e7d371cc
-- title:
--   Finite Section 9 payload from a rounded selector and guarded slack
-- statement:
--   Fix a regular mesh $M$ with $\delta>0$, a bridge with its canonical partition and moment-ready certificate, a compatible bank and guarded anchor certificate, and endpoint selector $s$. Assume $W\ge2$ dominates the reciprocal-prime quadrature cutoff; fixed-ratio prime count and occupancy hold at ratio $\rho>1$; $\rho^3<r_0$; and positive cell scale points are at least two. Let $T\ge0,N>0,d>0,\sigma>0$ satisfy $C_{\rm post}q/L\le TN/\log y$ and $LN=n$. Require the rounded-selector tangent input with the actual Proposition 8.7 pointwise bound and its ratio-cell tail bound, guarded endpoint slack for the same selector, $(K_0+1)h\le n$, divisibility of the fixed-factor charge into the precharged target, and the named fixed-component collision-free condition. The distributed main, error, and ceiling budgets must be at most $d^2/48,d^2/96,d^2/96$, respectively. For every split request in the canonical ratio-cell flow, its prescribed lower cardinality must be positive, at most the actual clean-list cardinality, and have product with either endpoint label at least $dn$. Then, retaining all parameters literally,
--
--   $$\mathrm{SectionNineFinalPayload}(s,\mathrm{canonicalRatioCellFlow}(s),L,\sigma)\ \wedge\ \mathrm{TangentRatioCellGeometry}(r_0).$$
--
--   This adapter uses only the rounded tangent input and guarded slack from the endpoint source; its finite analytic and collision hypotheses remain explicit.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSectionNineFinalGeometry.lean#L318-L624

import Definitions.Def_erdos390_remaining_analytic_propositions_004

theorem Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack_compact : Erdos390.RemainingAnalyticGoal004_011 := by sorry
