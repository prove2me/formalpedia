-- Prove2me | Theorems.Thm_Erdos390_WholePaper_sum_roughSaiasSelectorCellLedger_mul_fourth_le_compact
-- name    : Erdos390.WholePaper.sum_roughSaiasSelectorCellLedger_mul_fourth_le_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:51:04.31871+00:00
-- url     : https://prove2.me/theorems/95bd4f6e-e5b1-42bb-93f7-1664311771bf
-- title:
--   Fourth-power logarithmic weighting of selector ledgers
-- statement:
--   Let $C\ge0$, $X\in\mathbb N$ and $2\le M\le Z$ be natural numbers. Define $S_X(m)=\lfloor X/m\rfloor/\log m-\lfloor X/(m+1)\rfloor/\log(m+1)$. Then
--   $$\sum_{m=M}^{Z-1}S_X(m)\frac{Cm}{\log^4m}\le\frac{CX(2+\log Z)}{\log^5M}+\frac{CX(1+\log Z)}{\log^6M}.$$
--
--   This is the selector-ledger estimate compatible with the fourth-power prime-number-theorem error weight.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughSaiasSharpCorrectionTarget.lean#L1328-L1447

import Definitions.Def_erdos390_remaining_analytic_propositions_008

theorem Erdos390.WholePaper.sum_roughSaiasSelectorCellLedger_mul_fourth_le_compact : Erdos390.RemainingAnalyticGoal008_037 := by sorry
