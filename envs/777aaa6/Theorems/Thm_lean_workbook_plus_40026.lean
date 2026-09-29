-- Prove2me | Theorems.Thm_lean_workbook_plus_40026
-- name    : lean_workbook_plus_40026
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/c4cfedb3-af75-4f6d-b133-fbe13b336f59
-- statement:
--   Let $a,b,c,d \in \mathbb{R}_{+}$ and $a+b +c +d =1$ , show that $ ab +bc +cd \leq \dfrac{1}{4}. $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40026 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habc : a + b + c + d = 1) : a * b + b * c + c * d ≤ 1 / 4   :=  by sorry
