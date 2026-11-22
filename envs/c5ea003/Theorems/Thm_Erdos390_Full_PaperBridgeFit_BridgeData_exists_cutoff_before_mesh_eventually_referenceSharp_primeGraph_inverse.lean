-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_cutoff_before_mesh_eventually_referenceSharp_primeGraph_inverse
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_before_mesh_eventually_referenceSharp_primeGraph_inverse
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:53:10.562289+00:00
-- url     : https://prove2.me/theorems/610d1f2c-9849-4074-b375-587c86ba2a0c
-- title:
--   Cutoff-before-mesh reference sharp inverse
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. There exist a mesh tolerance $\tau>0$, an inverse constant $C_{\rm ref}>0$, and a cutoff $W_0$. For every $W\ge W_0$, every finite head set, and every regular relative mesh $M$ with $\delta>0$ and $\delta+M.\mathrm{ratio}\le\tau$, choose a nonempty set of positive cells with lower endpoints greater than $1/8$, upper endpoints at most $7/8$, and half their total width at least $1/8$. For all sufficiently large $n$, every bridge with sample size $n$, cutoff $W$, and the canonical partition of this mesh has an interval certificate and an invertible projected arithmetic reference sharp operator $T$ on its sharp gauge space satisfying
--
--   $$\|T^{-1}v\|\le C_{\rm ref}\|v\|\qquad\text{for every }v.$$
--
--   The cutoff and inverse constant precede the mesh quantifiers, so the bound is independent of the number of cells and the moving low-band center.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalPrimeGraphReferenceEventually.lean#L32-L266

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
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

universe u_1

theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_before_mesh_eventually_referenceSharp_primeGraph_inverse : Erdos390.RemainingAnalyticGoal001_013.{u_1} := by sorry
