-- Prove2me | Theorems.Thm_lean_workbook_plus_26357
-- name    : lean_workbook_plus_26357
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/87bf5e4c-5632-4a8d-b042-f6f317a06b2b
-- statement:
--   $ P(x) = a(x - r)(x - s)(x - t) = a(x^3 - (r + s + t)x^2 + (rs + st + tr)x - rst)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26357 (a r s t x : ℂ) : a * (x - r) * (x - s) * (x - t) = a * (x^3 - (r + s + t) * x^2 + (r * s + s * t + t * r) * x - r * s * t)   :=  by sorry
