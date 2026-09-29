-- Prove2me | Theorems.Thm_lean_workbook_plus_41792
-- name    : lean_workbook_plus_41792
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/49988685-aa57-4677-943d-6147cb70326f
-- statement:
--   Notice $i^2 = \frac{2\binom{2i}{2}+\binom{2i}{1}}{4}$\n\nYou can do the algebra or you can apply this neat bijection.\n\nNotice that $4i^2=(2i)^2$ is the number of ways to choose a ordered pair $(a,b)$ where $2i\ge a,b \ge 1$ .\n\nAnother way to count this is to do casework on whether $(a,b)$ are distinct or not. If they are distinct, there is $\binom{2i}{2}\cdot 2!=2\binom{2i}{2}$ (a,b). If not, there is $\binom{2i}{1}$ possible (a,b).This means $4i^2=2\binom{2i}{2}+\binom{2i}{1}$ or $i^2=\frac{2\binom{2i}{2}+\binom{2i}{1}}{4}=\frac{\binom{2i+1}{2}+\binom{2i}{2}}{4}=\frac{\binom{2i+2}{2}}{4}$\n\n $\sum_{i=1}^{n}i^2 =\frac{\binom{2i+3}{3}}{4}$ by Hockey Stick which is the desired equality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41792 : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, i^2 = (2 * n + 3).choose 3 / 4   :=  by sorry
