-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_weighted_sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le_compact
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.weighted_sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:33:18.238534+00:00
-- url     : https://prove2.me/theorems/1c90521c-4b4d-4bad-aba4-091d1e4d8893
-- title:
--   Weighted canonical guard power-row bound from the census
-- statement:
--   For a valuation law $\lambda$, put $\Delta_\lambda(p,q)=\operatorname{Cov}_\lambda(v_p,v_q)-\operatorname{Cov}_\lambda(\mathbf1_{p\mid m},\mathbf1_{q\mid m})$. Write $E_g(K,d)=(K^2+K)(7d+2d^2)$, the guard power-correction row error. Assume canonical sample data from a guard ledger with parameters $C_{\rm prom},C_{\rm bank}$, separated physical intervals, nonempty surviving cells, upper endpoints at most $C_{\max}$, and $W>1$. Let each raw medium score have absolute value at most $K_s$. Assume $e^{2K_s}\#\mathrm{guards}/\#S_c\le1/2$, the raw density lower bound $\#S_c\ge\mathrm{paperCellDensity}_c\,n/2$, and valuation envelope at most $C_e\log n$, with $C_e\ge0$. Put $D=\mathrm{canonicalGuardPerturbationConstant}(P,I,K_s)$ and $r_n=\mathrm{censusRatioMajorant}(C_{\rm prom},C_{\rm bank},n)$. Then
--
--   $$p\sum_q|\Delta_{\rm guarded\ medium}(p,q)-\Delta_{\rm raw\ medium}(p,q)|\le Y E_g(C_e\log n,Dr_n).$$
--
--   The displayed quantity is exactly the defined weighted guard majorant used downstream.
--
--   This compact declaration is definitionally identical to the original fully quantified statement; the named proposition preserves every hypothesis.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperBridgeCanonicalGuardPowerCorrection.lean#L499-L689

import Definitions.Def_erdos390_analytic_compact_goals_003

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.weighted_sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le_compact : Erdos390.AnalyticCompactBatch003Goal002.{u_1, u_2} := by sorry
