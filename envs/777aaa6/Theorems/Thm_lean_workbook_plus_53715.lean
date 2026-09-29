-- Prove2me | Theorems.Thm_lean_workbook_plus_53715
-- name    : lean_workbook_plus_53715
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/677b8c63-b63c-4e87-976e-abab61f4cb72
-- statement:
--   Let be $ x,y\in \mathbb{R}$ and $ k\in \mathbb{N}^*$ such that $ \{kx\}=\{ky\}$ and $ \{(k+1)x\}=\{(k+1)y\}$ . Show that : $ \{nx\}=\{ny\}\ ,\ (\forall)n\in \mathbb{N}^*$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53715 (x y : ℝ) (k : ℕ) (h1 : 0 < k) (h2 : (↑k * x) % 1 = (↑k * y) % 1) (h3 : ((↑k + 1) * x) % 1 = ((↑k + 1) * y) % 1) (n : ℕ) (hn : 0 < n) : (↑n * x) % 1 = (↑n * y) % 1   :=  by sorry
