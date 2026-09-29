-- Prove2me | Theorems.Thm_lean_workbook_plus_60671
-- name    : lean_workbook_plus_60671
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/c17aaf49-ecbc-4730-98e7-daade7cff2b2
-- statement:
--   prove that \((a^2+b^2+c^2)\cdot\frac{(p-1)^2}{2}\ge(ab+bc+ca)\cdot\frac{(p-1)^2}{2}\) for \(a,b,c,p\ge 0\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60671 (a b c p : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hp : p ≥ 0) : (a^2 + b^2 + c^2) * (p - 1)^2 / 2 ≥ (a * b + b * c + c * a) * (p - 1)^2 / 2   :=  by sorry
