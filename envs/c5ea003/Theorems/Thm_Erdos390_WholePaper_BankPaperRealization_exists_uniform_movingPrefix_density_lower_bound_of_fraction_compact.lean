-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_uniform_movingPrefix_density_lower_bound_of_fraction_compact
-- name    : Erdos390.WholePaper.BankPaperRealization.exists_uniform_movingPrefix_density_lower_bound_of_fraction_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:09:14.302142+00:00
-- url     : https://prove2.me/theorems/36e2de2e-c1eb-4b10-952b-6b2db2f5a2ff
-- title:
--   A moving prefix of positive relative length has uniform positive density
-- statement:
--   Fix a head pattern $P$, real $0<A<C$, and $r_{\min}>0$. There are $c_{\rm prefix}>0$ and $N_0$ such that for every $n\ge N_0$ and integer endpoint $k$ with $\lfloor An\rfloor<k\le\lfloor Cn\rfloor$ and normalized physical prefix fraction at least $r_{\min}$,
--   $$\lfloor Cn\rfloor>0,\qquad |\operatorname{structuredCell}(P,\lfloor An\rfloor,k,y_n)|\ge c_{\rm prefix}\lfloor Cn\rfloor.$$
--   Here the prefix fraction is exactly $(k/n-A)/(C-A)$, using the real physical endpoints before rounding. The lower bound is uniform over the moving endpoint.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosureMoving.lean#L258-L384

import Definitions.Def_erdos390_remaining_analytic_propositions_007

theorem Erdos390.WholePaper.BankPaperRealization.exists_uniform_movingPrefix_density_lower_bound_of_fraction_compact : Erdos390.RemainingAnalyticGoal007_007 := by sorry
