-- Prove2me | Theorems.Thm_lean_workbook_plus_49958
-- name    : lean_workbook_plus_49958
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/bdf4bc0c-ef15-446f-a463-78ccc425c6c4
-- statement:
--   $ r_{n} = 2 r_{n - 1} - 1 \iff (r_{n} - 1) = 2 (r_{n - 1} - 1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49958 (r : ℕ → ℤ) (n : ℕ) : (r n = 2 * r (n - 1) - 1) ↔ (r n - 1 = 2 * (r (n - 1) - 1))   :=  by sorry
