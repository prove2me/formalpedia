-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_boxIndependent_actual_component_signed_profiles
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_component_signed_profiles
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:55:31.986551+00:00
-- url     : https://prove2.me/theorems/27dc5844-2331-46d1-ad9c-99f3cc800652
-- title:
--   Uniform signed profiles for the full actual bridge component laws
-- statement:
--   For a divisor $D$, let $M_n(D)$ denote the common paper divisibility main term; write $w_{p,r}=(r+1)/p^r$ and $w_{p,q,r,s}=w_{p,r}w_{q,s}$. Fix a nonempty finite head set with patterns $H_h$, two fixed physical intervals $I$, a common upper bound $C_{\max}$, and guard ledgers with fixed promotion and bank parameters. Fix $W>1$ containing all head primes and a nonnegative effective prime-coefficient bound $A$. Assume each lower interval endpoint is at least one and every upper endpoint is at most $C_{\max}$. Fix also a nonnegative bound $A_{\rm phys}$ on the physical parameter. There exist a nonnegative sequence $E_n$ and $N_0$, independent of the later choice of band index set and bridge data, such that $E_n\to0$ and $E_n\log\log n\to0$. For any such bridge at $n\ge N_0$ whose head patterns, physical endpoints, guard set, and cutoff are exactly the prescribed ones, and whose effective prime coefficients are bounded by $A$, all component laws $\mu_c$ satisfy
--   $$|\mathbb E_{\mu_c}1_{pq\mid m}-M_n(pq)|\le4E_n/(pq),\qquad |\mathbb E_{\mu_c}1_{p\mid m}-M_n(p)|\le2E_n/p$$
--   for distinct moving-band primes $p,q$. Here $\mu_c$ is the full actual component valuation law, and the bridge parameter must also satisfy $|\xi_{\rm physical}|\le A_{\rm phys}$. Thus the common profile includes the valuation tilt, guard deletion, and physical tilt, while retaining the rate needed for sharp rows. The moving prime band is $\{p\text{ prime}:W<p\le\lfloor n^{2/9}\rfloor\}$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperActualSquarefreeReference.lean#L732-L991

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

theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_boxIndependent_actual_component_signed_profiles : Erdos390.RemainingAnalyticGoal001_010.{u_1, u_3} := by sorry
