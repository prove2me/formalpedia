-- Prove2me | Theorems.Thm_lean_workbook_plus_16528
-- name    : lean_workbook_plus_16528
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/b0172be1-897b-4960-afaf-869e04cc4439
-- statement:
--   Let $a,b,c,d \in \mathbb{Z}$ such that $ad-bc\neq 0$. Given that $ad-bc|b_1$ and $ad-bc|b_2$, prove that there exist integers $x$ and $y$ that simultaneously satisfy $ax+by=b_1$ and $cx+dy=b_2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16528 {a b c d b1 b2 : ℤ} (h : a * d - b * c ≠ 0) (h1 : a * d - b * c ∣ b1) (h2 : a * d - b * c ∣ b2) : ∃ x y, a * x + b * y = b1 ∧ c * x + d * y = b2   :=  by sorry
