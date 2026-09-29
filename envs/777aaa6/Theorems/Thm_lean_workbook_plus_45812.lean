-- Prove2me | Theorems.Thm_lean_workbook_plus_45812
-- name    : lean_workbook_plus_45812
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/e4f27cd9-9ade-4143-b3d4-115640fdaaf2
-- statement:
--   Count the set $\{k\mid (1\le k\le 2015)\wedge(11\mid a_k) \}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45812 (a : ℕ → ℕ) (h1 : ∀ k, a k = (11 * k)) : ∃ A, A = {k | (1 ≤ k ∧ k ≤ 2015) ∧ (11 ∣ a k)}   :=  by sorry
