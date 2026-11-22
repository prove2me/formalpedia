-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_paperFineMesh_cutoff_eventually_canonical_lemma86_relativePrimePower
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.exists_paperFineMesh_cutoff_eventually_canonical_lemma86_relativePrimePower
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:01:35.818909+00:00
-- url     : https://prove2.me/theorems/128b92b7-a145-4960-a834-6de285764a14
-- title:
--   Relative prime-power variance estimate with the same regression witness
-- statement:
--   For cMesh>0 there are a positive mesh tolerance, positive sharp and ordinary inverse constants, Crow≥0, Creg=2Csharp Crow≥0, Crel>0 and a cutoff W₀ preceding the mesh. Here a canonical bridge means the guarded canonical sample at the indicated n and W, with separated physical intervals, a nonempty remainder in each cell, and the canonical mesh prime partition. The finite nonempty head family has exactly the primes at most W in each head pattern. Physical interval endpoints lie between 1 and a fixed upper bound; guard ledgers have fixed promotion and bank parameters. The barycentric target has cell-mass margin at least a fixed positive marginFloor, and its baseline equals the bridge baseline. Conclusions are uniform on the closed effective-parameter ball of any fixed radius a ≥ 0. For a permitted mesh with δ>0 and w=δ+η within that tolerance, there is an eventually nonnegative ε_rel(n) with ε_rel→0 and ε_rel log L→0. Eventually the partition satisfies |dev|≤w, L₁(dev)≤7w, w²≤(456/cMesh²)V, V≤4w² and V≤centerEnergy. There is one common equivalence e_z equal to the actual nuisance-Schur map, with sharp and ordinary inverse bounds Csharp and Cordinary, slow residual rows bounded by Crow·wα_i, and a regression solving the literal normal equation with sharp norm at most Creg w. Its compensated coefficients have supremum at most (1+Creg)w, L¹ sum at most (7+2Creg log 4)w, and squared-L² sum at most 2(4+2Creg² log 4)w². For its regression q_z, the full post-band prime score and squarefree post-band score additionally satisfy the displayed relative variance bound.
--
--   $$|\operatorname{Var}_\xi(S_{\rm prime}(q_z))-\operatorname{Var}_\xi(S_{\rm sf}(q_z))|\le(C_{\rm rel}/W+\varepsilon_{\rm rel}(n))w^2.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalLemma86RelativePrimePowerEventually.lean#L56-L479

import Definitions.Def_erdos390_remaining_analytic_propositions_003
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

theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_paperFineMesh_cutoff_eventually_canonical_lemma86_relativePrimePower : Erdos390.RemainingAnalyticGoal003_001.{u_1} := by sorry
