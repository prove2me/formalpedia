-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_sum_abs_sameWeight_powerCorrection_sub_le_of_divisor_bounds_compact
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_sameWeight_powerCorrection_sub_le_of_divisor_bounds_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:03:52.71604+00:00
-- url     : https://prove2.me/theorems/84314102-9e3f-4aa2-90ef-ede58007922a
-- title:
--   Divisor perturbations control a common-mixture power row
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, and $\mathcal P=\{p\text{ prime}:W<p\le Y\}$. For a valuation law $\lambda$, put $\Delta_\lambda(p,q)=\operatorname{Cov}_\lambda(v_p,v_q)-\operatorname{Cov}_\lambda(\mathbf1_{p\mid m},\mathbf1_{q\mid m})$. Let common finite weights mix pairs of bounded-valuation laws $\mu_c,\nu_c$ with common bound $M$, and let $W>1$, $\epsilon,G\ge0$. Suppose for all cells and positive $D$, $\mathbb E_{\mu_c}\mathbf1_{D\mid m}\le G/D$ and the two divisor probabilities differ by at most $8\epsilon G/D$. Suppose their divisor-pair covariances differ by at most $8\epsilon(G/\operatorname{lcm}(D,E)+3G^2/(DE))$ for every positive $D,E$. Then
--
--   $$\sum_{q\in\mathcal P}|\Delta_\nu(p,q)-\Delta_\mu(p,q)|\le\mathrm{physicalPowerCorrectionMixtureBudget}(\epsilon,G,n,W,p).$$
--
--   This is the finite core of the residual physical-score comparison.
--
--   This compact declaration is definitionally identical to the original fully quantified statement; the named proposition preserves every hypothesis.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperBridgePhysicalPowerCorrectionRow.lean#L1123-L1345

import Definitions.Def_erdos390_analytic_compact_goals

universe u_3 u_4

theorem Erdos390.Full.PaperBridgeFit.BridgeData.sum_abs_sameWeight_powerCorrection_sub_le_of_divisor_bounds_compact : Erdos390.AnalyticCompactGoal004.{u_3, u_4} := by sorry
