-- Prove2me | Theorems.Thm_lean_workbook_plus_30983
-- name    : lean_workbook_plus_30983
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/b3bb184c-1a6f-4519-875a-fa9f8309a74f
-- statement:
--   If $ a = b = 2c$ and $ abc = 864$ , then the value of $ a + b + c$ is equal: \n\n a) 16 \n b) 23 \n c) 30 \n d) 32 \n e) 34
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30983 (a b c : ℝ) (h₁ : a = b ∧ b = 2*c) (h₂ : a*b*c = 864) : a + b + c = 30   :=  by sorry
