-- Prove2me | Theorems.Thm_lean_workbook_plus_57364
-- name    : lean_workbook_plus_57364
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/ed683321-c8f8-49ec-9ef4-b3d526b4225f
-- statement:
--   Define $P_i$ to be the probability that the ant stays on the same side after $i$ more moves if the previous move stayed on the same side (top or bottom). Define $Q_i$ to be the probability that the ant stays on the same side after $i$ more moves if the previous move switched between top and bottom. After switching sides, the next move cannot, so $Q_i = P_{i-1}$ . We also have the recursion $P_{i+1} = \frac 12 P_i + \frac 12 (1-Q_i) = \frac 12 (P_i - P_{i-1} + 1)$ since with one-half probability it stays on the same side and with one-half probability, it switches sides and the probability that we return to the original is $1-Q_i$ . \n\n We wish to compute $\frac 23(1-P_7) + \frac 13 Q_7$ . It is easy to see that $P_1 = \frac 12$ and $P_2 = \frac 14$ . \n\n Now, using the recursion $P_{i+1} = \frac 12 P_i + \frac 12 (1-P_{i-1}) = \frac 12 (P_i - P_{i-1} + 1)$ we compute \n\n $ \begin{tabular}{c | c} n & P_n \ 1 & \frac 12 \ 2 & \frac 14 \ 3 & \frac 38 \ 4 & \frac{9}{16} \ 5 & \frac{19}{32} \ 6 & \frac{33}{64} \ 7 & \frac{59}{128} \ \end{tabular} $ \n\n at which point it is easy to compute $\frac 23(1-P_7) + \frac 13 Q_7 = \frac{17}{32}\rightarrow \boxed{049}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57364  (p q : ℕ → ℚ)
  (h₀ : p 1 = 1 / 2)
  (h₁ : p 2 = 1 / 4)
  (h₂ : ∀ n, p (n + 2) = 1 / 2 * p (n + 1) + 1 / 2 * (1 - p n))
  (h₃ : ∀ n, q (n + 1) = p n)
  (h₄ : 0 < 7) :
  (2 / 3 * (1 - p 7) + 1 / 3 * q 7) = 17 / 32   :=  by sorry
