-- Prove2me | Theorems.Thm_lean_workbook_plus_46031
-- name    : lean_workbook_plus_46031
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/b242658f-1dca-4421-ba00-6eff3b3f47f5
-- statement:
--   Given $b=4095$ and $p^k=13$ where $p$ is a prime, calculate $(p^k)^3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46031 (b : ℕ) (p : ℕ) (k : ℕ) (h₁ : b = 4095) (h₂ : p^k = 13) : (p^k)^3 = 2197   :=  by sorry
