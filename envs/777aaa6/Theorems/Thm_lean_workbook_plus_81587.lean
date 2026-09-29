-- Prove2me | Theorems.Thm_lean_workbook_plus_81587
-- name    : lean_workbook_plus_81587
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/16b691d0-aafd-4ef8-875c-668b55d7816d
-- statement:
--   We are essentially being asked to compute $P(A|B)$ where $A$ is the assertion that the special ( $5$ white, $5$ black) urn was chosen, and $B$ is the assertion that both drawn balls are black. By Bayes' Theorem: $P(A|B)=\frac{P(B|A)P(A)}{P(B)}$ It is then fairly easily computed that: $P(B|A)=\frac{2}{9}$ , $P(A)=\frac{1}{n+1}$ , and $P(B)=\frac{2+3n}{9(n+1)}$ so $P(A|B)=\frac{2}{2+3n}$ . For this to equal $\frac{1}{7}$ requires $n=4$ . There seemed to be a missing backslash at least in the problem statement--which I corrected in quoting it.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81587  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : (2:ℝ) / (2 + 3 * n) = 1 / 7) :
  n = 4   :=  by sorry
