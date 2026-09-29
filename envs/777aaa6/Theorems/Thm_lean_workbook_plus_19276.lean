-- Prove2me | Theorems.Thm_lean_workbook_plus_19276
-- name    : lean_workbook_plus_19276
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/0949f092-b144-431b-bbb5-ac82a2157c1a
-- statement:
--   For prime numbers $ p$ and $ q$ , $ p+q = 102$ and $ p>q.$ What is the least possible value of $ p-q$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19276 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p > q) (h : p + q = 102) : 16 ≤ p - q   :=  by sorry
