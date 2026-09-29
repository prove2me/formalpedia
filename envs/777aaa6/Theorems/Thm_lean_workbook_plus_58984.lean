-- Prove2me | Theorems.Thm_lean_workbook_plus_58984
-- name    : lean_workbook_plus_58984
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/f59c3b95-935e-402c-89fa-4a3a7e94e379
-- statement:
--   (a) \n\n $\sum{\frac{bc+2}{a^{2}+2}}\geq 3$ $\Leftrightarrow$ $\sum{\frac{bc+2}{a^{2}+2}-1}\geq 0$ \n\n $\Leftrightarrow$ $\sum{\frac{2(bc-a^{2})}{a^{2}+2}}\geq 0$ ,but \n\n $\sum{\frac{2(bc-a^{2})}{a^{2}+2}}=\sum{\frac{(b-a)(c+a)+(c-a)(b+a)}{a^{2}+2}}=\sum{(b-a)(\frac{a+c}{a^{2}+2}-\frac{b+c}{b^{2}+2})}=\sum{\frac{(a-b)^{2}}{(a^{2}+2)(b^{2}+2)}}\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58984 c a : ℝ) : (b * c + 2) / (a ^ 2 + 2) + (c * a + 2) / (b ^ 2 + 2) + (a * b + 2) / (c ^ 2 + 2) ≥ 3 ↔ (b * c + 2) / (a ^ 2 + 2) - 1 + (c * a + 2) / (b ^ 2 + 2) - 1 + (a * b + 2) / (c ^ 2 + 2) - 1 ≥ 0   :=  by sorry
