-- Prove2me | Theorems.Thm_lean_workbook_plus_34238
-- name    : lean_workbook_plus_34238
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/959caf1e-2f21-452c-b492-3e5b33b27fac
-- statement:
--   Prove that for any three real numbers x, y, z, we have $ x^2 + y^2 + z^2\geq \frac13\left(x + y + z\right)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34238 (x y z : ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ (1 / 3) * (x + y + z) ^ 2   :=  by sorry
