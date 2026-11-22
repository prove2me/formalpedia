-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice_compact
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:15:59.859578+00:00
-- url     : https://prove2.me/theorems/ab17fe81-ecb0-4c1d-9f5a-19a3bfab17aa
-- title:
--   Canonical moving-prime marked row from a Schur decomposition
-- statement:
--   Fix physical intervals between 1 and U≥1 and a guard ledger. There is a cutoff W₀ before all subsequent head and effective-ball choices. For W≥W₀, choose nonnegative CinvOrd,Tband,targetScale,Creg, positive γslow, a finite nonempty head family supported on primes ≤W, and a ball radius and positive target margin. There is Crow≥0 chosen before the relative mesh. For every mesh with δ>0, eventually any bridge whose sample equals the guarded canonical sample, whose physical intervals are separated and whose guarded cells remain nonempty, whose partition is the canonical mesh partition, and whose scale is w=δ+η has the following property. The barycentric target has the stated positive cell-mass margin and its baseline equals the bridge baseline. Suppose the full covariance has a positive gap on the ball; a family e_z equals the actual nuisance-Schur operator; its ordinary inverse norm is at most CinvOrd; the two-stage slow variance is at least γslow w²; the compensated target is at most w·targetScale; the projected band target norm is at most Tband; and the actual regression sharp norm is at most Creg w. For any finite set of monitored band primes, the covariance between marked valuation and the target vector-field score satisfies the displayed bound throughout the ball. The constant does not depend on the mesh.
--
--   $$\left|\operatorname{Cov}_{\xi(z)}\!\left(v_p,\operatorname{score}(\operatorname{vectorField}(\operatorname{targetVector}(\Delta),\xi(z)))\right)\right|\le C_{\rm row}/p.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperProposition87CanonicalMarkedProfilesEventually.lean#L38-L562

import Definitions.Def_erdos390_remaining_analytic_propositions_001

universe u_1

theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice_compact : Erdos390.RemainingAnalyticGoal001_014.{u_1} := by sorry
