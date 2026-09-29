-- Prove2me | Theorems.Thm_lean_workbook_plus_76336
-- name    : lean_workbook_plus_76336
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/9167b0a7-0512-4314-8917-af939197a9e9
-- statement:
--   b) A closed subset of $[a,b]$ is compact.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76336 (a b : ℝ) (hab : a ≤ b) (s : Set ℝ) (hs : a ≤ b ∧ b ≤ a) : IsClosed s → s ⊆ Set.Icc a b → IsCompact s   :=  by sorry
