-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_sum_abs_actual_powerCorrection_sub_physicalMedium_le_compact
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_actual_powerCorrection_sub_physicalMedium_le_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:33:10.61071+00:00
-- url     : https://prove2.me/theorems/47556e72-57df-4a7b-8f2a-ef3eb559ad81
-- title:
--   Actual versus medium-only power correction under the same weights
-- statement:
--   For a valuation law $\lambda$, put $\Delta_\lambda(p,q)=\operatorname{Cov}_\lambda(v_p,v_q)-\operatorname{Cov}_\lambda(\mathbf1_{p\mid m},\mathbf1_{q\mid m})$. Let $B$ have nonempty head set and $W>1$, and fix a tilt parameter $\xi$. Suppose positive cell densities $\rho_c$ obey $\#S_c\ge\rho_c\mathrm{hi}_c$. Let $A,A_{\rm phys},K_{\rm phys},G\ge0$ bound, respectively, every effective prime coefficient, the physical tilt coordinate, the absolute physical score, and each reciprocal-event constant $$\exp\!\left(2\frac A{B.L}\frac{\log\mathrm{hi}_c}{\log W}\right)/\rho_c\le G.$$ Assume $8A_{\rm phys}K_{\rm phys}/B.L\le1$. Then
--
--   $$\sum_q|\Delta_{\rm actual}(p,q)-\Delta_{\rm medium}(p,q)|\le\mathrm{physicalPowerCorrectionMixtureBudget}(A_{\rm phys}K_{\rm phys}/B.L,G,n,W,p).$$
--
--   The reference removes only the residual physical score, retaining the actual reweighted component probabilities.
--
--   This compact declaration is definitionally identical to the original fully quantified statement; the named proposition preserves every hypothesis.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperBridgePhysicalPowerCorrectionRow.lean#L1347-L1467

import Definitions.Def_erdos390_analytic_compact_goals_003

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_actual_powerCorrection_sub_physicalMedium_le_compact : Erdos390.AnalyticCompactBatch003Goal001.{u_1, u_2} := by sorry
