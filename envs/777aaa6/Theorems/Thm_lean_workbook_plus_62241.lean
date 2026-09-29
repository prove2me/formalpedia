-- Prove2me | Theorems.Thm_lean_workbook_plus_62241
-- name    : lean_workbook_plus_62241
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/2ba85161-aee6-451b-ac6c-d8d20c2b7ab2
-- statement:
--   Let $h_i$ ( $-1\le i\le 4,i\neq0$ ) be the probability that we have a run of $5$ heads before $2$ tails if our current streak of heads is $i,$ where a streak of $-1$ is a tail. Notice \begin{align*}h_4&=\tfrac{1}{2}+\tfrac{1}{2}h_{-1}\h_3&=\tfrac{1}{2}h_4+\tfrac{1}{2}h_{-1}\h_2&=\tfrac{1}{2}h_3+\tfrac{1}{2}h_{-1}\h_1&=\tfrac{1}{2}h_2+\tfrac{1}{2}h_{-1}\h_{-1}&=\tfrac{1}{2}h_1+\tfrac{1}{2}\cdot 0\end{align*} where we are considering whether the next flip is heads or tails. Repeatedly substituting yields \n\n \begin{align*}h_1&=\tfrac{1}{2}h_2+\tfrac{1}{2}h_{-1}&=\tfrac{1}{2}(\tfrac{1}{2}h_3+\tfrac{1}{2}h_{-1})+\tfrac{1}{2}h_{-1}&=\tfrac{1}{4}(\tfrac{1}{2}h_4+\tfrac{1}{2}h_{-1})+\tfrac{3}{4}h_{-1}&=\tfrac{1}{8}(\tfrac{1}{2}+\tfrac{1}{2}h_{-1})+\tfrac{7}{8}h_{-1}&=\tfrac{1}{16}+\tfrac{15}{16}h_{-1}&=\tfrac{1}{16}+\tfrac{15}{16}(\tfrac{1}{2}h_1+\tfrac{1}{2}\cdot 0)&=\tfrac{1}{16}+\tfrac{15}{32}h_1\end{align*} so $h_1=\tfrac{2}{17}$ and $h_{-1}=\tfrac{1}{17}.$ Our answer is $$\frac{1}{2}\left(\frac{2}{17}+\frac{1}{17}\right)=\boxed{\frac{3}{34}}.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62241 :
  (1 / 2 * (2 / 17 + 1 / 17)) = 3 / 34   :=  by sorry
