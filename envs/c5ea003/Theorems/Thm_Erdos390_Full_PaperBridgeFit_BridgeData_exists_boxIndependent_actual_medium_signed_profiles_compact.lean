-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_boxIndependent_actual_medium_signed_profiles_compact
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_medium_signed_profiles_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:11:28.997199+00:00
-- url     : https://prove2.me/theorems/6b6e2e22-e7f6-47b1-b7c8-4b6ee27d1993
-- title:
--   Uniform signed profiles for the actual guarded medium-tilted cells
-- statement:
--   For a divisor $D$, let $M_n(D)$ denote the common paper divisibility main term; write $w_{p,r}=(r+1)/p^r$ and $w_{p,q,r,s}=w_{p,r}w_{q,s}$. Fix a nonempty finite head set with patterns $H_h$, two fixed physical intervals $I$, a common upper bound $C_{\max}$, and guard ledgers with fixed promotion and bank parameters. Fix $W>1$ containing all head primes and a nonnegative effective prime-coefficient bound $A$. Assume each upper interval endpoint is at least one and at most $C_{\max}$. There exist a nonnegative sequence $E_n$ and $N_0$, independent of the later choice of band index set and bridge data, such that $E_n\to0$ and $E_n\log\log n\to0$. For any such bridge at $n\ge N_0$ whose head patterns, physical endpoints, guard set, and cutoff are exactly the prescribed ones, and whose effective prime coefficients are bounded by $A$, all component laws $\mu_c$ satisfy
--   $$|\mathbb E_{\mu_c}1_{pq\mid m}-M_n(pq)|\le4E_n/(pq),\qquad |\mathbb E_{\mu_c}1_{p\mid m}-M_n(p)|\le2E_n/p$$
--   for distinct moving-band primes $p,q$. Here $\mu_c$ is the actual guarded medium-tilted cell law. This attaches the abstract marked profiles to the concrete bridge using only structural identifications. The moving prime band is $\{p\text{ prime}:W<p\le\lfloor n^{2/9}\rfloor\}$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperActualSquarefreeReference.lean#L291-L569

import Definitions.Def_erdos390_remaining_analytic_propositions_001

universe u_1 u_3

theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_medium_signed_profiles_compact : Erdos390.RemainingAnalyticGoal001_011.{u_1, u_3} := by sorry
