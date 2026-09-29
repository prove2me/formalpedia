-- Prove2me | Theorems.Thm_lean_workbook_plus_45249
-- name    : lean_workbook_plus_45249
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/1e10d4c4-addf-4a3d-b30e-5ee36a2843d3
-- statement:
--   Definition of Euler's totient function $\varphi(n)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45249 : ∀ n : ℕ, 1 < n → ∑ k in Finset.filter (fun k => Nat.gcd k n = 1) (Finset.Icc 1 n), 1 = Nat.totient n   :=  by sorry
