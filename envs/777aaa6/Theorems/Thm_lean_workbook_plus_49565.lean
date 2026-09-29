-- Prove2me | Theorems.Thm_lean_workbook_plus_49565
-- name    : lean_workbook_plus_49565
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/cef9e995-43de-4725-b8e8-ade732e9e97f
-- statement:
--   Prove that:\n$$\sum_{cyc}\left(1-\frac{3}{a^2+2}\right)=\sum_{cyc}\frac{a^2-1}{a^2+2}=\sum_{cyc}\left(\frac{a^2-1}{a^2+2}+\frac{a^2-6a+5}{6}\right)=\sum_{cyc}\frac{(a-1)^2(a-2)^2}{6(a^2+2)}\geq0$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49565 :
  ∀ a b c : ℝ,
    (a - 1) ^ 2 * (b - 2) ^ 2 / (6 * (a ^ 2 + 2)) +
    (b - 1) ^ 2 * (c - 2) ^ 2 / (6 * (b ^ 2 + 2)) +
    (c - 1) ^ 2 * (a - 2) ^ 2 / (6 * (c ^ 2 + 2)) ≥
    0   :=  by sorry
