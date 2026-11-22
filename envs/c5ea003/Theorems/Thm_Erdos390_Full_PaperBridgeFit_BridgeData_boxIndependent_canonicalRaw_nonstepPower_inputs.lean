-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_boxIndependent_canonicalRaw_nonstepPower_inputs
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.boxIndependent_canonicalRaw_nonstepPower_inputs
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:58:36.82523+00:00
-- url     : https://prove2.me/theorems/9381aaed-4636-4cf6-b68b-a9f9bf92914b
-- title:
--   Uniform raw reference inputs for non-step prime-power rows
-- statement:
--   Fix a finite nonempty head family, physical intervals with lower endpoints at least 1 and upper endpoints at most Cmax, and a guard ledger. The box-independent prime-power constant Cpow is positive. For W>1 containing all head primes and nonnegative coefficient and physical tilt bounds, there exists a nonnegative sequence ε₇₅ tending to zero, with ε₇₅ log L tending to zero. The canonical non-step correction ρ also satisfies ρ log L→0. Beyond one threshold, uniformly over finite band types, canonical guarded bridges and allowed tilts, the canonical raw medium reference law satisfies PrimePowerTransferBounds(Cpow,ε₇₅), and the actual/reference prime-power covariance differences satisfy the displayed weighted row estimate.
--
--   $$p\sum_q|(\operatorname{cov}_{VV}-\operatorname{cov}_{II})_{\rm actual}(p,q)-(\operatorname{cov}_{VV}-\operatorname{cov}_{II})_{\rm raw}(p,q)|\le\rho(n).$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalNonstepPowerInputsEventually.lean#L97-L245

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

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.boxIndependent_canonicalRaw_nonstepPower_inputs : Erdos390.RemainingAnalyticGoal001_008.{u_1, u_2} := by sorry
