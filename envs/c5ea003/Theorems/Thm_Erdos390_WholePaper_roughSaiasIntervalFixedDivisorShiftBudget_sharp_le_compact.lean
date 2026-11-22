-- Prove2me | Theorems.Thm_Erdos390_WholePaper_roughSaiasIntervalFixedDivisorShiftBudget_sharp_le_compact
-- name    : Erdos390.WholePaper.roughSaiasIntervalFixedDivisorShiftBudget_sharp_le_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:47:15.969793+00:00
-- url     : https://prove2.me/theorems/4d25c84e-c8fe-407b-8408-c2c308a12e2e
-- title:
--   Explicit inverse-log-square majorant for the interval shift budget
-- statement:
--   For natural A,B,y,d with y≥2, d>0 and A≤B, let C⋆ denote roughSaiasSharpDefectConstant and use the sharp endpoint rate η(y)=10C⋆/(log y)². Denote by Bη(A,B;y,d) the source interval fixed-divisor budget: 6+(B−A)(log d+2)/(d log y)+Pη(⌊A/d⌋,⌊B/d⌋;y)+Pη(A,B;y)/d, where Pη(a,b;y)=η(y)(a+b)+5(b−a)/log y. Then this abstract budget is bounded by the explicit sharp budget below. No condition d≤A or upper restriction on log B is required for this deterministic comparison.
--
--   $$B_\eta(A,B;y,d)\le6+\frac5{\log y}+\frac{(B-A)(\log d+12)}{d\log y}+\frac{20C_\star(A+B)}{d(\log y)^2}.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughSaiasSharpFixedHeadIntervalShift.lean#L475-L585

import Definitions.Def_erdos390_remaining_analytic_propositions_008

theorem Erdos390.WholePaper.roughSaiasIntervalFixedDivisorShiftBudget_sharp_le_compact : Erdos390.RemainingAnalyticGoal008_028 := by sorry
