-- Prove2me | Theorems.Thm_lean_workbook_plus_21515
-- name    : lean_workbook_plus_21515
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/e086577f-b0b3-46ec-9ccf-5fda82a610e7
-- statement:
--   If $ n$ is prime then $ \phi(n) = n-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21515 (n : ℕ) (hn : Nat.Prime n) : Nat.totient n = n-1   :=  by sorry
