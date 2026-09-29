-- Prove2me | Theorems.Thm_lean_workbook_plus_6710
-- name    : lean_workbook_plus_6710
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/7b7e68dd-4f85-47d1-9e4e-92805875dc5d
-- statement:
--   Euuuh, just basic $ (x-u)(x-v)(x-w)=x^3-(u+v+w)x^2+(uv+vw+wu)x-uvw$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6710 : ∀ u v w x : ℂ, (x - u) * (x - v) * (x - w) = x^3 - (u + v + w) * x^2 + (u * v + v * w + w * u) * x - u * v * w   :=  by sorry
