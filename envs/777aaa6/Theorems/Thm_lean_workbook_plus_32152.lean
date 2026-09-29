-- Prove2me | Theorems.Thm_lean_workbook_plus_32152
-- name    : lean_workbook_plus_32152
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c913b54c-0ef6-4b62-a057-db428e6570e8
-- statement:
--   Given $0<x<\pi/2$ ; we see that $ 0 \le \sin (2x) \le 1 \implies 0 \le 2 \sin x \ \cos x \le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32152 : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ 2 * Real.sin x * Real.cos x ∧ 2 * Real.sin x * Real.cos x ≤ 1   :=  by sorry
