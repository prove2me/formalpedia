-- Prove2me | Theorems.Thm_lean_workbook_plus_67383
-- name    : lean_workbook_plus_67383
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/78842dcc-02d5-4022-876f-6e0a209076d5
-- statement:
--   For prime numbers $ p$ and $ q$ , $ p + q = 102$ and $ p > q.$ What is the least possible value of $ p - q$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67383 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p > q) (h : p + q = 102) : p - q ≥ 3   :=  by sorry
