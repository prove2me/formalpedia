-- Prove2me | Theorems.Thm_lean_workbook_plus_51332
-- name    : lean_workbook_plus_51332
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/6dc9383a-887a-4ad2-8574-7c3a5a4fcc7e
-- statement:
--   The probability that his subset has at least one lit candle can be split into 4 cases (the case where there are $0$ lit candles is not needed as there is no subset that has $1$ or more lit candles) \n\nCase 1: $1$ of the candles is lit, $3$ are not. \n\nThe chance of this happening is $4*(\frac{1}{2})^4$ and the probability that the subset has at least one lit candle is $\frac{1}{2}$ . The total probability of this is $4*(\frac{1}{2})^4 * \frac{1}{2} = \frac{1}{8}$ \n\nCase 2: $2$ of the candles are lit, $2$ are not. \n\n $6*(\frac{1}{2})^4 * \frac{12}{16} = \frac{9}{32}$ \n\nCase 3: $3$ of the candles are lit, $1$ is not. \n\n $4*(\frac{1}{2})^4 * \frac{14}{16} =\frac{7}{32} $ \n\nCase 4: all $4$ of the candles are lit. \n\n $(\frac{1}{2})^4 * \frac{15}{16} = \frac{15}{256}$ \n\nSumming these all together we get the probability that his subset contains at least one lit candle is $\boxed{\frac{175}{256}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51332 (4*(1/2)^4 * 1/2) + (6*(1/2)^4 * 12/16) + (4*(1/2)^4 * 14/16) + ((1/2)^4 * 15/16) = 175/256   :=  by sorry
