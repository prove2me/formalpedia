-- Prove2me | Theorems.Thm_lean_workbook_plus_16819
-- name    : lean_workbook_plus_16819
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/9f7f6db6-09fd-4def-b55f-457e1305f9dc
-- statement:
--   Show that if $a + b = c + d$ and $h = f$ then $a + b + h = c + d + f$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16819 (a b c d h f : ℝ) (h₁ : a + b = c + d) (h₂ : h = f) : a + b + h = c + d + f   :=  by sorry
