-- Prove2me | Theorems.Thm_lean_workbook_plus_73621
-- name    : lean_workbook_plus_73621
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/41896cbf-f996-455d-a233-105084d78018
-- statement:
--   $\\sqrt{k}$ is an integer if and only if $k$ is a perfect square (k is the square of an integer).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73621 (k : ℕ) : (∃ x : ℕ, x^2 = k) ↔ (∃ x : ℕ, x = Real.sqrt k)   :=  by sorry
