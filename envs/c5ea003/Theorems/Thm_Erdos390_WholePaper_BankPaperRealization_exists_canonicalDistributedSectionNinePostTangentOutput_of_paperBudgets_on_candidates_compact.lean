-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates_compact
-- name    : Erdos390.WholePaper.BankPaperRealization.exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:27:34.511946+00:00
-- url     : https://prove2.me/theorems/c0e62d4b-eb77-47a5-a7fc-b8ad9273ca9a
-- title:
--   Distributed tangent correction on a guarded candidate set
-- statement:
--   Fix a bank realization $R$ at size $n>0$, a guarded central-anchor certificate, finite exceptional and fixed factor sets, a finite candidate set $A$, and a rounded selector $s$ satisfying the canonical tangent-input conditions for a finite band/cell partition of the tangent primes. Write $r_p$ for its tangent residual, $F$ for the canonical ratio-cell earthmover flow, and $\mathcal L_j$ for the prescribed clean multiplier list of split request $j$. Assume positive $d,L,\sigma,N$ with $LN=n$, positive fixed factors and divisibility of their selector tail charge into the precharged target. Every prime lies at or below its band's last cell, and every cell through that last cell is occupied. Assume the weighted residual and port bounds $p|r_p|\le R_*$ and $p\,\mathrm{port}_p\le P_*$, total traffic at most $T H Nw+e_TN$, and $R_*+2P_*\le IHNw+e_IN$. The paper main, error and ceiling budgets are at most $d^2/48,d^2/96,d^2/96$, respectively. Each split request has positive canonical lower cardinality $\ell_j\le|\mathcal L_j|$, with $dn\le\ell_j$ times either endpoint label. Every allowed multiplier places both endpoints in $A$, where both selector values belong to $[\sigma/L,1-\sigma/L]$. All lists use the specified natural parameters $W,K,h,X_0$, dedicated rows and numerical guard set.
--
--   Then multipliers $m_j\in\mathcal L_j$ can be chosen with all numerical endpoints distinct, and there is a canonical post-tangent output whose selector is exactly the distributed update of $s$. In particular, writing $u_j,v_j,w_j$ for request source, target and weight and $D_q$ for the selector valuation deficit,
--   $$\operatorname{div}F(p)=r_p,\qquad \sum_jw_j\bigl(v_q(u_j)-v_q(v_j)\bigr)=D_q\quad(q\in\mathbb N).$$
--
--   This assembles collision-free tangent exactification while retaining an arbitrary guarded candidate support.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalDistributedCandidateSet.lean#L422-L856

import Definitions.Def_erdos390_remaining_analytic_propositions_007

universe u_1

theorem Erdos390.WholePaper.BankPaperRealization.exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates_compact : Erdos390.RemainingAnalyticGoal007_001.{u_1} := by sorry
