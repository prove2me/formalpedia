-- Prove2me | solution 1 for lean_workbook_plus_51854
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:39.628162+00:00
-- url     : https://prove2.me/submissions/96ced4c2-3590-4eb3-81ec-1aedc0a01eff

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} : (a - b) ^ 2 * (1 / 2 * a ^ 4 + 5 / 2 * a ^ 2 * b ^ 2 + 1 / 2 * b ^ 4 + 1 / 2 * c ^ 4) + (b - c) ^ 2 * (1 / 2 * b ^ 4 + 5 / 2 * b ^ 2 * c ^ 2 + 1 / 2 * c ^ 4 + 1 / 2 * a ^ 4) + (c - a) ^ 2 * (1 / 2 * c ^ 4 + 5 / 2 * c ^ 2 * a ^ 2 + 1 / 2 * a ^ 4 + 1 / 2 * b ^ 4) + 2 * (a ^ 2 * (a - b) ^ 2 * (a - c) ^ 2 + b ^ 2 * (b - a) ^ 2 * (b - c) ^ 2 + c ^ 2 * (c - a) ^ 2 * (c - b) ^ 2) + (a - b) ^ 4 * c ^ 2 + (b - c) ^ 4 * a ^ 2 + (c - a) ^ 4 * b ^ 2 + 5 / 2 * (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 ≥ 0 := by
  (intros; positivity)
