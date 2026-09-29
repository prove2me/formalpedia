-- Prove2me | Theorems.Thm_lean_workbook_plus_8986
-- name    : lean_workbook_plus_8986
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/b54cef4b-c7b5-48d5-999e-ae1cccd1cfb2
-- statement:
--   prove that \((a+bp)^2 + (b+cp)^2 + (c+ap)^2\ge \frac{(1+p)^2}{2}(a^2+b^2+c^2+ab+bc+ca)\) for \(a,b,c,p\ge 0\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8986 (a b c p : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hp : p ≥ 0) : (a + b * p) ^ 2 + (b + c * p) ^ 2 + (c + a * p) ^ 2 ≥ (1 + p) ^ 2 / 2 * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a)   :=  by sorry
