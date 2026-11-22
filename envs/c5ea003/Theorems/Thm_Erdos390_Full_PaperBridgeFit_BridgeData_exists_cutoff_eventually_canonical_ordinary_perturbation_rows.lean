-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_exists_cutoff_eventually_canonical_ordinary_perturbation_rows
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_eventually_canonical_ordinary_perturbation_rows
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:59:38.50379+00:00
-- url     : https://prove2.me/theorems/64530ccc-d943-40fe-a9df-e5d2f21127c2
-- title:
--   Three canonical ordinary perturbation estimates
-- statement:
--   Fix Cref>0 and Rproj≥0. There is a cutoff W₀ chosen before the finite head family, physical intervals, guard ledger and effective ball. Head primes need only be at most W. For W≥W₀, Here a canonical bridge means the guarded canonical sample at the indicated n and W, with separated physical intervals, a nonempty remainder in each cell, and the canonical mesh prime partition. Physical interval endpoints lie between 1 and a fixed upper bound; guard ledgers have fixed promotion and bank parameters. The barycentric target has cell-mass margin at least a fixed positive marginFloor, and its baseline equals the bridge baseline. Conclusions are uniform on the closed effective-parameter ball of any fixed radius a ≥ 0. For an arbitrary finite nonempty band type assume ∑H_jα_j≤Rproj∑H_jα_j². Eventually, for every raw-gauge q and every band i, the squarefree/reference and full/squarefree row differences are bounded by the canonical ordinary row tolerance τ=canonicalOrdinaryRowTolerance(Cref,Rproj). The actual nuisance-Schur/full-map difference is bounded by σ=canonicalOrdinarySchurTolerance(Cref).
--
--   $$|R_{\rm sf}(q)_i-R_{\rm ref}(q)_i|\le\tau\|q\|_\infty,\quad |R_{\rm full}(q)_i-R_{\rm sf}(q)_i|\le\tau\|q\|_\infty,\quad \|(S-F)q\|_\infty\le\sigma\|q\|_\infty.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalActualSchurOrdinaryRowsEventually.lean#L144-L605

import Definitions.Def_erdos390_remaining_analytic_propositions_001
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

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_cutoff_eventually_canonical_ordinary_perturbation_rows : Erdos390.RemainingAnalyticGoal001_015.{u_1, u_2} := by sorry
