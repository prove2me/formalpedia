-- Prove2me | Theorems.Thm_lean_workbook_plus_79130
-- name    : lean_workbook_plus_79130
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/b1eb1e1f-5a9c-48ff-a414-54d13f283bfa
-- statement:
--   Just so we are clear, I did switch the $ p$ and $ 1 - p$ in my first post but otherwise it is correct. In[6]:= Reduce[{a == (p) + (1 - p) a^2, p >= 0, 1 >= p, a >= 0, 1 >= a}, a] Out[6]= (0 <= p < 1/2 && (a == p/(1 - p) || a == 1)) || (1/2 <= p <= 1 && a == 1)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79130 (a = p + (1-p)*a^2 ∧ p >= 0 ∧ p <= 1 ∧ a >= 0 ∧ a <= 1) ↔ (p >= 0 ∧ p <= 1/2 ∧ a = p/(1-p)) ∨ (p >= 1/2 ∧ p <= 1 ∧ a = 1)   :=  by sorry
