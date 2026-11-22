-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_paperFineMesh_cutoff_eventually_canonical_lemma86_variance_of_base
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.exists_paperFineMesh_cutoff_eventually_canonical_lemma86_variance_of_base
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:01:40.070669+00:00
-- url     : https://prove2.me/theorems/4590b0d4-e4eb-4182-8bec-480f09d9bdd4
-- title:
--   Canonical two-sided slow variance from fixed-witness base outputs
-- statement:
--   Fix cMesh>0 and Creg≥0. There are meshTol,γslow,Cvar>0 and W₀ preceding the mesh. Here a canonical bridge means the guarded canonical sample at the indicated n and W, with separated physical intervals, a nonempty remainder in each cell, and the canonical mesh prime partition. The finite nonempty head family has exactly the primes at most W in each head pattern. Physical interval endpoints lie between 1 and a fixed upper bound; guard ledgers have fixed promotion and bank parameters. The barycentric target has cell-mass margin at least a fixed positive marginFloor, and its baseline equals the bridge baseline. Conclusions are uniform on the closed effective-parameter ball of any fixed radius a ≥ 0. For W≥W₀ and a permitted mesh with δ>0 and w=δ+η≤meshTol, eventually the following holds for every point z and every raw-band equivalence e. Assume its actual regression satisfies ‖q‖sharp≤Creg w and the same partition has |dev|≤w, L₁≤7w, w²≤(456/cMesh²)V, V≤4w² and V≤centerEnergy. Then its two-stage compensated variance obeys the following two-sided bound. The result needs no additional analytic-error assumptions.
--
--   $$\gamma_{\rm slow}w^2\le V_2(z,e)\le C_{\rm var}w^2.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalLemma86RemainingOutputsEventually.lean#L157-L720

import Definitions.Def_erdos390_remaining_analytic_propositions_003
import Definitions.Def_erdos390_analytic_nonstep_certificate
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

theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_paperFineMesh_cutoff_eventually_canonical_lemma86_variance_of_base : Erdos390.RemainingAnalyticGoal003_002.{u_1} := by sorry
