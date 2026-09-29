-- Prove2me | Theorems.Thm_lean_workbook_plus_9909
-- name    : lean_workbook_plus_9909
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/57dce2bf-273a-43a9-b841-6738e992b472
-- statement:
--   $ \phi(n)$ is the number of residues $ \mod n$ that are coprime to $ n$ . As $ 1$ is coprime to $ n$ , we get $ \phi(n)\geq 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9909  (n : ℕ)
  (h₀ : 0 < n) :
  1 ≤ φ n   :=  by sorry
