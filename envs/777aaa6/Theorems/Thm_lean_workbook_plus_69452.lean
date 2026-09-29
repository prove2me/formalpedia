-- Prove2me | Theorems.Thm_lean_workbook_plus_69452
-- name    : lean_workbook_plus_69452
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/9a2c459e-6852-45fa-ad74-761a1cac5dc3
-- statement:
--   If $ a + b = c$ , then $ a^2 + b^2 \geq \frac {c^2}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69452 (a b c : ℝ) (hab : a + b = c) : a^2 + b^2 ≥ c^2 / 2   :=  by sorry
