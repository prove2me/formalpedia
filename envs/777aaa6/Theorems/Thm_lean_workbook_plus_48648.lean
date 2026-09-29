-- Prove2me | Theorems.Thm_lean_workbook_plus_48648
-- name    : lean_workbook_plus_48648
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/f15dbdc7-b7e8-4e6d-acf6-9d7d85a8ff90
-- statement:
--   For $n = a + k$, where $a = \lfloor n \rfloor$ and $0 < k < 1$, prove that $\lfloor n \rfloor + 1 = \lceil n \rceil$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48648 (n a k : ℝ) (h₁ : n = a + k) (h₂ : a = ⌊n⌋) (h₃ : 0 < k) (h₄ : k < 1) : ⌊n⌋ + 1 = ⌈n⌉   :=  by sorry
