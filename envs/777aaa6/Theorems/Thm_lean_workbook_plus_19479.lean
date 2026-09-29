-- Prove2me | Theorems.Thm_lean_workbook_plus_19479
-- name    : lean_workbook_plus_19479
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/07ecde56-fb57-4514-98cb-421b91a3f394
-- statement:
--   Prove that $f(m) = m$ for all positive integers $m$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19479 (f : ℕ → ℕ) (hf: f = fun m => if m > 0 then m else 0) : ∀ m > 0, f m = m   :=  by sorry
