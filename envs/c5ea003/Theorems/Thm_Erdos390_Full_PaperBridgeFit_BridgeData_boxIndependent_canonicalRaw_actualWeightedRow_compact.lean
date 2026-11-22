-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_boxIndependent_canonicalRaw_actualWeightedRow_compact
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.boxIndependent_canonicalRaw_actualWeightedRow_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:12:49.839078+00:00
-- url     : https://prove2.me/theorems/3f54ef3d-cfc2-4d84-8cb2-7c34e5d9f544
-- title:
--   Canonical actual covariance row with separate sharp remainders
-- statement:
--   Fix a finite nonempty head family $P$, physical intervals $I$ with lower endpoints at least one and upper endpoints at most $C_{\max}$, and a guard ledger at every $n$ with fixed census constants $C_{\rm prom},C_{\rm bank}$. For a valuation law $\lambda$, put $\Delta_\lambda(p,q)=\operatorname{Cov}_\lambda(v_p,v_q)-\operatorname{Cov}_\lambda(\mathbf1_{p\mid m},\mathbf1_{q\mid m})$. Let $C_*$ be the fixed box-independent prime-power constant. After choosing $W>1$ above all head primes, then $A_c,A_p\ge0$, there exist a nonnegative $\epsilon_n$ and threshold $N_0$ such that $\epsilon_n\to0$ and $\epsilon_n\log\log n\to0$. Write $G=\mathrm{canonicalPhysicalPowerCorrectionConstant}(P,I,C_{\max},W,A_c)$, $e_n=A_p\log C_{\max}/\log n$, and $R_n=\mathrm{physicalPowerCorrectionRowError}(e_n,G,n,W)$. Put $C_e=\mathrm{valuationLogCoefficient}(C_{\max},W)$, $D=\mathrm{canonicalGuardPerturbationConstant}(P,I,A_cC_e)$, and $T_n=R_n+\mathrm{guardPowerCorrectionWeightedMajorant}(C_{\rm prom},C_{\rm bank},C_e,D,n)$. Then $T_n\log\log n\to0$. The estimates hold uniformly for every later finite band partition, bridge $B$, and tilt parameter $\xi$ at ambient $n\ge N_0$, provided its cutoff is $W$, its sample data equal the canonical constructor with separated intervals and nonempty surviving cells, every effective prime coefficient is at most $A_c$ in absolute value, and the physical coordinate has absolute value at most $A_p$.
--
--   $$C_*>0,\qquad p\sum_q|\Delta_{\rm actual}(p,q)|\le\frac{C_*}{W}+\epsilon_n+T_n.$$
--
--   The raw-law remainder and the actual/reference correction remain separate, with their precise rates exposed for the moving-low argument.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalActualPrimePowerWeightedRowEventually.lean#L30-L192

import Definitions.Def_erdos390_remaining_analytic_propositions_001

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.boxIndependent_canonicalRaw_actualWeightedRow_compact : Erdos390.RemainingAnalyticGoal001_006.{u_1, u_2} := by sorry
