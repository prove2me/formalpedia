-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_boxIndependent_canonicalRaw_fullSharp
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.boxIndependent_canonicalRaw_fullSharp
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:58:14.855327+00:00
-- url     : https://prove2.me/theorems/0f8e3679-4be5-4cc9-9ea3-70883ac6c60b
-- title:
--   Canonical sharp-row transfer with box-independent leading constant
-- statement:
--   Fix a finite nonempty head family $P$, physical intervals $I$ with lower endpoints at least one and upper endpoints at most $C_{\max}$, and a guard ledger at every $n$ with fixed census constants $C_{\rm prom},C_{\rm bank}$. Let $C_*$ be the fixed box-independent prime-power constant. After choosing $W>1$ above all head primes, then $A_c,A_p\ge0$, there exist a nonnegative $\epsilon_n$ and threshold $N_0$ such that $\epsilon_n\to0$ and $\epsilon_n\log\log n\to0$. Write $G=\mathrm{canonicalPhysicalPowerCorrectionConstant}(P,I,C_{\max},W,A_c)$, $e_n=A_p\log C_{\max}/\log n$, and $R_n=\mathrm{physicalPowerCorrectionRowError}(e_n,G,n,W)$. Put $C_e=\mathrm{valuationLogCoefficient}(C_{\max},W)$, $D=\mathrm{canonicalGuardPerturbationConstant}(P,I,A_cC_e)$, and $T_n=R_n+\mathrm{guardPowerCorrectionWeightedMajorant}(C_{\rm prom},C_{\rm bank},C_e,D,n)$. Then $T_n\log\log n\to0$. The estimates hold uniformly for every later finite band partition, bridge $B$, and tilt parameter $\xi$ at ambient $n\ge N_0$, provided its cutoff is $W$, its sample data equal the canonical constructor with separated intervals and nonempty surviving cells, every effective prime coefficient is at most $A_c$ in absolute value, and the physical coordinate has absolute value at most $A_p$. Write $H_T=\sum_{W<p\le\lfloor n^{2/9}\rfloor}t_p/p$, with $t_p=\log p/\log(n^{2/9})$. For every band function $q$ with $|q_j|\le1$ and every cell $i$ of center $c_i$,
--
--   $$C_*>0,\qquad|\mathrm{fullSharpRow}(q,i)-\mathrm{squarefreeSharpRow}(q,i)|\le\frac{3C_*(H_T+1)}W+\frac{3\epsilon_n(H_T/c_i+1)}W+\frac{T_n}{c_i}.$$
--
--   All raw analytic, guard, and physical error inputs are constructed internally; only the canonical realization and genuine coefficient box are required at use.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperBridgeCanonicalPowerCorrectionTriangle.lean#L567-L739

import Definitions.Def_erdos390_remaining_analytic_propositions_001
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

universe u_1 u_3

theorem Erdos390.Full.PaperBridgeFit.BridgeData.boxIndependent_canonicalRaw_fullSharp : Erdos390.RemainingAnalyticGoal001_007.{u_1, u_3} := by sorry
