-- Prove2me | Theorems.Thm_lean_workbook_plus_19951
-- name    : lean_workbook_plus_19951
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/1c4cf67f-e523-44af-afb2-3ea6a0d43c43
-- statement:
--   Using the Arithmetic Mean-Geometric Mean inequality, $\left(\frac{(a^2+b^2+c^2)}{3}\right)^3 \geq \frac{27}{8}(a^2+b^2)(b^2+c^2)(c^2+a^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19951 (a b c : ℝ) :
  (3 * (a^2 + b^2 + c^2) / 3)^3 ≥ (27 / 8) * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2)   :=  by sorry
