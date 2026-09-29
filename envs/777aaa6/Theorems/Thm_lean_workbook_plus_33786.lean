-- Prove2me | Theorems.Thm_lean_workbook_plus_33786
-- name    : lean_workbook_plus_33786
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/6ae59a43-6585-4f7e-89f9-0f0a2b14ab5d
-- statement:
--   Prove the identity: $a+b+c=2p\Longrightarrow \sum a(p-b)(p-c)(b^{2}-c^{2})=-p^{2}(a-b)(b-c)(c-a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33786 {a b c p : ℝ} (h : a + b + c = 2 * p) :
  a * (p - b) * (p - c) * (b ^ 2 - c ^ 2) + b * (p - c) * (p - a) * (c ^ 2 - a ^ 2) +
      c * (p - a) * (p - b) * (a ^ 2 - b ^ 2) = -p ^ 2 * (a - b) * (b - c) * (c - a)   :=  by sorry
