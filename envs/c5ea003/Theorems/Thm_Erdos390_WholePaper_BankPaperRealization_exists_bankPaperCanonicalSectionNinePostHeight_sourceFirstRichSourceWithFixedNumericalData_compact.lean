-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstRichSourceWithFixedNumericalData_compact
-- name    : Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstRichSourceWithFixedNumericalData_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:27:24.123318+00:00
-- url     : https://prove2.me/theorems/8923af97-a794-4886-85be-2555c7160d89
-- title:
--   Rich source geometry preserves fixed numerical choices across meshes
-- statement:
--   Write $L_n=\log n$, $s_n=n/\log n$, $y_n=\lfloor n^{2/9}\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le y_n\}$. Fix $c>C_0$, a paper combined-charge exponent $\delta_*$, $W>0$, protected and active coefficients $\beta_p\ge0$, $\beta_a>0$ with $\beta_p+\beta_a\le c/\rho_h(W)$, and multiplicity $K_0+1\ge1/\rho_h(W)$, where $\rho_h$ is the rough-head density; assume $W\ge2d+1$. Let $F$ be a guarded tail family whose certificates satisfy the combined anchor/bank capacity divisibility, base-bank and selector-charge divisibilities into the precharged target, and both exact target-product identities. For each prime $p\le2d+1$, require the precharged target valuation to exceed the selector-charge valuation by at least $(c-C_0)s_n/[24(p-1)]$. In addition, fix positive $c_s,c_u$, a positive natural exponent $E$, and the source-cell margin equal to the canonical head margin (using $E$, the uniform head linear floor, and $c_u$) times the fixed physical interpolation margin. Assume
--   $$c_s s_n\le\widetilde q_n\le c_u s_n\quad\text{eventually},\qquad2\sum_{p\le W}C_{\rm head}(c,p)\le E c_s/4.$$
--   For every regular relative mesh of positive width, there exist total tail-indexed rich source data and their exact images under the canonical source-bridge/target construction. Eventually these sources have index $n$, cutoff $W$, synchronized smooth mass at least one, separated head patterns, active support in the guarded smooth row, valid coefficient boxes, and rounded-source residual inputs. Their head reserve has exponent exactly $E$, target exactly the residual tail prime-valuation vector, and active mass $\widetilde q_n$; the source target has at least the fixed cell margin. The residual head coordinates lie between the canonical linear floor times $s_n$ and $C_{\rm head}(c,p)s_n$. Their sample data are exactly the canonical guarded cells, and the bank and bridge guards agree. Thus the rich geometry and the simpler bridge/target data stay pointwise synchronized.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSectionNinePostHeightSourceFirstRichSourceWithFixedNumericalData.lean#L45-L949

import Definitions.Def_erdos390_remaining_analytic_propositions_006

theorem Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstRichSourceWithFixedNumericalData_compact : Erdos390.RemainingAnalyticGoal006_001 := by sorry
