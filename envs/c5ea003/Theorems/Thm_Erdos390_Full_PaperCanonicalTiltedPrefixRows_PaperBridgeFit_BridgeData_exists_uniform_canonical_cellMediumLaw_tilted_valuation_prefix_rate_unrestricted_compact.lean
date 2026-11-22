-- Prove2me | Theorems.Thm_Erdos390_Full_PaperCanonicalTiltedPrefixRows_PaperBridgeFit_BridgeData_exists_uniform_canonical_cellMediumLaw_tilted_valuation_prefix_rate_unrestricted_compact
-- name    : Erdos390.Full.PaperCanonicalTiltedPrefixRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_tilted_valuation_prefix_rate_unrestricted_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:14:52.790093+00:00
-- url     : https://prove2.me/theorems/ea7ccfd1-c423-4ba7-ab49-48630965aa22
-- title:
--   Canonical guard-deleted valuation-prefix covariance rate
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. Fix a finite nonempty head index set, patterns $P_h$, physical intervals $I$, guard constants $C_{\rm prom},C_{\rm bank}$ and a ledger $G_n$ at each $n$. Fix $W>1$ with all head primes at most $W$, and $A_{\rm coef}\ge0$. Consider any finite band set and bridge $B$ with sample size $n$, cutoff $W$, separated physical intervals, and nonempty cells after deleting the ledger guards; require its sample data to equal the canonical sample data for these choices. Let $\xi$ be any parameter whose effective prime coefficients have absolute value at most $A_{\rm coef}$, and let $\mu_c^\xi$ be its medium law on cell $c$. There exist a nonnegative sequence $\epsilon_n$ and a threshold independent of the later bridge and parameter, with $\epsilon_n\log L_n\to0$, such that eventually, for every band prime $p$, cell $c$, and integer $k\ge0$,
--
--   $$|\operatorname{Cov}_{\mu_c^\xi}(v_p,\mathbf1_{m\le k})|\le\epsilon_n/p.$$
--
--   This is the canonical all-prefix estimate after guard deletion, uniform over subsequent bridge choices.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalTiltedPrefixRows.lean#L236-L484

import Definitions.Def_erdos390_remaining_analytic_propositions_004

universe u_1 u_2

theorem Erdos390.Full.PaperCanonicalTiltedPrefixRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_tilted_valuation_prefix_rate_unrestricted_compact : Erdos390.RemainingAnalyticGoal004_003.{u_1, u_2} := by sorry
