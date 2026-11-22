-- Prove2me | Theorems.Thm_Erdos390_Full_PaperCanonicalTiltedValuationMeanRows_PaperBridgeFit_BridgeData_exists_uniform_canonical_cellMediumLaw_valuation_mean_profiles_rate_unrestricted_compact
-- name    : Erdos390.Full.PaperCanonicalTiltedValuationMeanRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_valuation_mean_profiles_rate_unrestricted_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:18:49.053614+00:00
-- url     : https://prove2.me/theorems/e7d79a96-b249-451c-80d7-9717e3845607
-- title:
--   Canonical valuation mean bound and pairwise agreement rate
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. Fix a finite nonempty head index set, patterns $P_h$, physical intervals $I$, guard constants $C_{\rm prom},C_{\rm bank}$ and a ledger $G_n$ at each $n$. Fix $W>1$ with all head primes at most $W$, and $A_{\rm coef}\ge0$. Consider any finite band set and bridge $B$ with sample size $n$, cutoff $W$, separated physical intervals, and nonempty cells after deleting the ledger guards; require its sample data to equal the canonical sample data for these choices. Let $\xi$ be any parameter whose effective prime coefficients have absolute value at most $A_{\rm coef}$, and let $\mu_c^\xi$ be its medium law on cell $c$. There exist $A_{\rm val}\ge0$, a nonnegative sequence $\epsilon_n$, and a common threshold with $\epsilon_n\log L_n\to0$, such that eventually, for every band prime $p$ and cells $c,c\prime$,
--
--   $$\mathbb E_{\mu_c^\xi}v_p\le A_{\rm val}/p,\qquad |\mathbb E_{\mu_c^\xi}v_p-\mathbb E_{\mu_{c\prime}^\xi}v_p|\le\epsilon_n/p.$$
--
--   A single reciprocal first-moment constant and a vanishing mean-agreement rate work for every later bridge and admissible parameter.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalTiltedValuationMeanRows.lean#L38-L443

import Definitions.Def_erdos390_remaining_analytic_propositions_004

universe u_1 u_2

theorem Erdos390.Full.PaperCanonicalTiltedValuationMeanRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_valuation_mean_profiles_rate_unrestricted_compact : Erdos390.RemainingAnalyticGoal004_004.{u_1, u_2} := by sorry
