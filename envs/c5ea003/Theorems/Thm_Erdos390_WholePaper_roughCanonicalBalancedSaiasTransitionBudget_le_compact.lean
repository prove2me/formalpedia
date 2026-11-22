-- Prove2me | Theorems.Thm_Erdos390_WholePaper_roughCanonicalBalancedSaiasTransitionBudget_le_compact
-- name    : Erdos390.WholePaper.roughCanonicalBalancedSaiasTransitionBudget_le_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:09:39.284349+00:00
-- url     : https://prove2.me/theorems/4bd876f3-740f-4357-9ead-6f98f3292c58
-- title:
--   Balanced Saias transition budget at the canonical row scale
-- statement:
--   Write $L=\log n$, $Y_n=\lfloor n^{2/9}\rfloor$, $h=\lceil cn/\log n\rceil$, and $K=K_0+1$. Fix natural W and $K_0$, real $\beta$, and $c>0$. Let $n\ge2$, $0<r\le n$, $y\ge2$, $L\ge1$, $\log y\ge L/5$, $h\le2cn/L$, and $Kh\le n$. Put $x=\lfloor n/r\rfloor$, use the source head density and balanced alpha, and take the four physical endpoints $\lfloor(2n+h)/r\rfloor$, $\lfloor2n/r\rfloor$, $\lfloor(2n-Kh)/r\rfloor$, and x. The source physical Saias transition budget $\mathcal S$, using the inverse-log-square endpoint rate at the sharp Saias defect constant, satisfies
--
--   $$\mathcal S\le C_{\rm trans}(W,K_0,c,\beta)(x/L^2+1).$$
--
--   Here $C_{\rm trans}$ is the sharp transition-row scale constant.
--
--   The three weighted sharp Saias pair budgets have the same uniform scale as the Dickman contribution.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughSaiasSharpCanonicalRowPaperScale.lean#L1075-L1520

import Definitions.Def_erdos390_remaining_analytic_propositions_008

theorem Erdos390.WholePaper.roughCanonicalBalancedSaiasTransitionBudget_le_compact : Erdos390.RemainingAnalyticGoal008_015 := by sorry
