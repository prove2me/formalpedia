-- Prove2me | Theorems.Thm_lean_workbook_plus_19943
-- name    : lean_workbook_plus_19943
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/5016556f-dfef-43f0-8e80-5c9828fe8000
-- statement:
--   prove that for all $(a,b) \in \mathbb{R}^2$ : \n $ \begin{cases} \frac{a}{a^2+1} \le \frac{1}{2}\ \frac{b}{b^2+1} \le \frac{1}{2} \end{cases} \Rightarrow \frac{a}{a^2+1}+\frac{b}{b^2+1} \le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19943 (a b : ℝ) (ha : a / (a ^ 2 + 1) ≤ 1 / 2) (hb : b / (b ^ 2 + 1) ≤ 1 / 2) : a / (a ^ 2 + 1) + b / (b ^ 2 + 1) ≤ 1   :=  by sorry
