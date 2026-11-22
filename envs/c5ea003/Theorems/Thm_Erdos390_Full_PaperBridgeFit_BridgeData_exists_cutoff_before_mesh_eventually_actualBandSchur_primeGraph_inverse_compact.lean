-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_cutoff_before_mesh_eventually_actualBandSchur_primeGraph_inverse_compact
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_before_mesh_eventually_actualBandSchur_primeGraph_inverse_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:14:49.303678+00:00
-- url     : https://prove2.me/theorems/4ae5e3e6-fa1a-4c9b-8c83-a21e03312b5e
-- title:
--   Uniform sharp inverse for the canonical actual nuisance-Schur operator
-- statement:
--   There exist positive constants meshTol and Cschur and a cutoff W₀, chosen before the mesh, head family, and effective ball. For W ≥ W₀, let M be a relative mesh with δ > 0 and δ + M.ratio ≤ meshTol. Suppose its nonempty anchor cells have lower endpoints greater than 1/8, upper endpoints at most 7/8, and total width at least 1/4. Here a canonical bridge means the guarded canonical sample at the indicated n and W, with separated physical intervals, a nonempty remainder in each cell, and the canonical mesh prime partition. The finite nonempty head family has exactly the primes at most W in each head pattern. Physical interval endpoints lie between 1 and a fixed upper bound; guard ledgers have fixed promotion and bank parameters. The barycentric target has cell-mass margin at least a fixed positive marginFloor, and its baseline equals the bridge baseline. Conclusions are uniform on the closed effective-parameter ball of any fixed radius a ≥ 0. Eventually in n, every such bridge with W > 1 admits linear equivalences e_z equal to its actual nuisance-Schur band operator S_z, whose inverses satisfy the following bound in the paper sharp norm. This supplies an actual, rather than reference, inverse for the later regression construction.
--
--   $$e_z=S_z,\qquad \|e_z^{-1}v\|_{\mathrm{sharp}}\le C_{\mathrm{schur}}\|v\|_{\mathrm{sharp}}.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalPrimeGraphActualSchurEventually.lean#L36-L410

import Definitions.Def_erdos390_remaining_analytic_propositions_001

universe u_1

theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_before_mesh_eventually_actualBandSchur_primeGraph_inverse_compact : Erdos390.RemainingAnalyticGoal001_012.{u_1} := by sorry
