-- Prove2me | Theorems.Thm_Erdos390_Full_PaperCanonicalMarkedNuisanceRows_PaperBridgeFit_BridgeData_exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall_compact
-- name    : Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:14:36.313889+00:00
-- url     : https://prove2.me/theorems/7ad2606d-092b-4687-8f5d-a636743f7373
-- title:
--   Canonical nuisance-valuation rate on every fixed effective ball
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. Fix a finite nonempty head family $P_h$, physical intervals satisfying $1\le I_\sigma^{\rm lower}<I_\sigma^{\rm upper}\le U$ with $U\ge1$, guard ledgers, and a cutoff $W>1$ containing all head primes. For any radius $a\ge0$ there are a nonnegative rate $\epsilon_n$ and a threshold, with $\epsilon_n\log L_n\to0$, such that the following holds uniformly for every finite band set and canonical guard-deleted bridge with separated intervals and nonempty remaining cells. At any effective parameter $z$ with $\|z\|\le a$, write $\mu_z$ for the tilted law and $N_c$ for a nuisance statistic. Then eventually
--
--   $$|\operatorname{Cov}_{\mu_z}(N_c,v_p)|\le\epsilon_n/p\qquad(c\text{ any nuisance coordinate},\ p\in\mathcal P_{n,W}).$$
--
--   The radius is chosen after the cutoff and is unrestricted; this rate is the marked nuisance input for Schur-complement estimates.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalMarkedNuisanceRows.lean#L36-L278

import Definitions.Def_erdos390_remaining_analytic_propositions_004

universe u_1 u_2

theorem Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall_compact : Erdos390.RemainingAnalyticGoal004_002.{u_1, u_2} := by sorry
