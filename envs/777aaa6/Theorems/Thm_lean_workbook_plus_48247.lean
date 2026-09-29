-- Prove2me | Theorems.Thm_lean_workbook_plus_48247
-- name    : lean_workbook_plus_48247
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/1475cbd8-4cea-443d-9a1b-5588ecd7a02f
-- statement:
--   Let $n$ be a positive integer number and $x_n=(3+\sqrt 5)^n+(3-\sqrt 5)^n$ . Prove that : $2^n|x_n\ ,\ \forall\ n\in\mathbb{N}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48247 (n : ℕ) (hn : 0 < n) (x_n : ℝ) (hx_n : x_n = (3 + Real.sqrt 5)^n + (3 - Real.sqrt 5)^n) : 2^n ∣ x_n   :=  by sorry
