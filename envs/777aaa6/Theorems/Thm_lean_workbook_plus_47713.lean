-- Prove2me | Theorems.Thm_lean_workbook_plus_47713
-- name    : lean_workbook_plus_47713
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/6d660f36-3d78-4c7f-b76a-0f21b238cd26
-- statement:
--   $x^{9k}+x^{8k}+x^{7k}+x^{6k}+x^{5k}+x^{4k}+x^{3k}+x^{2k}+x^{1k}+1 = (x^{1k}+1)(x^{4k}-x^{3k}+x^{2k}-x^{1k}+1)(x^{4k}+x^{3k}+x^{2k}+x^{1k}+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47713 (x : ℤ) (k : ℕ) : (x^((9:ℕ)*k) + x^((8:ℕ)*k) + x^((7:ℕ)*k) + x^((6:ℕ)*k) + x^((5:ℕ)*k) + x^((4:ℕ)*k) + x^((3:ℕ)*k) + x^((2:ℕ)*k) + x^((1:ℕ)*k) + 1) = (x^((1:ℕ)*k) + 1) * (x^((4:ℕ)*k) - x^((3:ℕ)*k) + x^((2:ℕ)*k) - x^((1:ℕ)*k) + 1) * (x^((4:ℕ)*k) + x^((3:ℕ)*k) + x^((2:ℕ)*k) + x^((1:ℕ)*k) + 1)   :=  by sorry
