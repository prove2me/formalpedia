-- Prove2me | Theorems.Thm_lean_workbook_plus_37833
-- name    : lean_workbook_plus_37833
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/721725e1-1d53-4874-8755-8c9298dc7544
-- statement:
--   Let $ y^2 = a$ and $ z^3 = a$ . Then $ (\frac {y}{z})^6 = \frac {y^6}{z^6} = \frac {a^3}{a^2} = a$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37833  (y z a : ℂ)
  (h₀ : y^2 = a)
  (h₁ : z^3 = a) :
  (y / z)^6 = a   :=  by sorry
