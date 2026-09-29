-- Prove2me | Theorems.Thm_lean_workbook_plus_10279
-- name    : lean_workbook_plus_10279
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2b945d80-fce1-4107-8c58-0b3fdd291040
-- statement:
--   the idea was an identity $a^3+b^3+c^3-3abc=(a+b+c)(a^2+b^2+c^2-ab-ac-bc)$ \n\n your inequality is \n\n $\frac {2(a^3+b^3+c^3)} {abc} -6+\frac {9(a+b+c)^2}{a^2+b^2+c^2} -27 \ge 0 \Leftrightarrow$ \n\n $2\frac {a^3+b^3+c^3-3abc} {abc}-18\frac {a^2+b^2+c^2-ab-bc-ca}{a^2+b^2+c^2}\ge 0 \Leftrightarrow$ \n\n $2\frac {(a+b+c)(a^2+b^2+c^2-ab-bc-ca)} {abc}-18\frac {a^2+b^2+c^2-ab-bc-ca}{a^2+b^2+c^2}\ge 0 \Leftrightarrow$ \n\n $(a^2+b^2+c^2-ab-bc-ca) (2\frac {a+b+c} {abc}-\frac {18}{a^2+b^2+c^2})\ge 0 \Leftrightarrow$ \n\n $(a^2+b^2+c^2-ab-bc-ca)\frac{2(a+b+c)(a^2+b^2+c^2)-18abc} {abc(a^2+b^2+c^2)}\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10279 :  ∀ a b c : ℝ, (2 * (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) - 6 + (9 * (a + b + c) ^ 2) / (a ^ 2 + b ^ 2 + c ^ 2) - 27) ≥ 0   :=  by sorry
