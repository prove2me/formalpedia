-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_structural_cutoff_eventually_canonical_actualFullQuotient_compact
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.exists_structural_cutoff_eventually_canonical_actualFullQuotient_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:16:00.694532+00:00
-- url     : https://prove2.me/theorems/f79edd17-191c-459f-9921-39f63ecfed20
-- title:
--   Structural cutoff for the canonical full quotient covariance gap
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. There exist $\kappa>0$ and $W_0$ chosen before all subsequent data. For any $W\ge W_0$, choose a regular relative mesh $M$ with $\delta>0$ and a nonempty anchor-cell set whose lower endpoints exceed $1/8$, upper endpoints are at most $7/8$, and half the sum of widths is at least $1/8$. Choose a finite nonempty head family whose prime support is exactly all primes at most $W$, physical intervals between $1$ and $U\ge1$, guard ledgers, an effective radius $a\ge0$, and a positive cell-mass margin floor. For all sufficiently large $n$, consider any canonical guard-deleted bridge with these data, separated intervals, nonempty remaining cells, the canonical mesh partition, and a barycentric target having at least that margin and giving the bridge baseline. For every $\|z\|\le a$, every band coefficient vector $b$, and every real $\mu$,
--
--   $$\kappa\,\|\operatorname{gaugePart}(b)\|_{\rm band}^2\le\operatorname{Var}_{\mu_z}\!\left(\operatorname{Res}_{\rm nuis}\bigl[\operatorname{PrimeScore}(\operatorname{residual}(b,\mu))\bigr]\right).$$
--
--   The residual, band norm, and nuisance regression are those of the bridge partition; nuisance regression uses the canonical positive gap at radius $3a$.
--
--   This gives a structural coercivity constant on the full arithmetic quotient, uniformly in the scalar residual parameter.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalFullQuotientEventually.lean#L62-L559

import Definitions.Def_erdos390_remaining_analytic_propositions_003

universe u_1

theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_structural_cutoff_eventually_canonical_actualFullQuotient_compact : Erdos390.RemainingAnalyticGoal003_003.{u_1} := by sorry
