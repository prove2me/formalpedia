-- Prove2me | Theorems.Thm_Erdos390_WholePaper_eventually_tangentPaper_candidateFloor_absorbs_canonicalLosses_compact
-- name    : Erdos390.WholePaper.eventually_tangentPaper_candidateFloor_absorbs_canonicalLosses_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:33:21.419095+00:00
-- url     : https://prove2.me/theorems/ac34e799-f4d7-42f6-83bb-d9f93aff2daa
-- title:
--   Canonical candidate floors absorb all clean-list losses
-- statement:
--   Fix $W,K\in\mathbb N$, $c>0$, $1<r_0<3/2$ and $0<\delta<1/18$ with $80C_M\delta<g=d_W(2-r_0)$. Set $h=h_n(c)$ and use the canonical cutoff $X_0(n,\delta)$ and density $g/16$. Eventually, for every $0<v\le u\le y(n)$ with $u/v\le r_0$, the broad multiplier interval is ordered and
--   $$\lfloor n/v\rfloor\le\lfloor\mathrm{BroadUpper}(n,K,h)/u\rfloor,\qquad L_{\rm eff}+E_{\rm nat}+4+4M_{\rm sharp}(n)\le L_{\rm candidate}.$$
--   Here $L_{\rm eff}$ is the effective lower cardinality at density $g/16$ and endpoint $v$, $E_{\rm nat}$ is the canonical exceptional natural upper bound for $(n,K,h,X_0,y,u,v)$, and $L_{\rm candidate}$ is the rough-head candidate lower floor.
--
--   This discharges the arithmetic comparison required for the canonical clean-list bridge.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/TangentPaperCleanListAbsorption.lean#L795-L1051

import Definitions.Def_erdos390_remaining_analytic_propositions_008

theorem Erdos390.WholePaper.eventually_tangentPaper_candidateFloor_absorbs_canonicalLosses_compact : Erdos390.RemainingAnalyticGoal008_009 := by sorry
