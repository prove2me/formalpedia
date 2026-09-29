-- Prove2me | solution 1 for lean_workbook_plus_34560
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:16:51.518095+00:00
-- url     : https://prove2.me/submissions/f03efdf7-0646-4ef4-839a-dc32a3a795f6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^3 * b + b^3 * c + c^3 * a - a^2 * b * c - a * b^2 * c - a * b * c^2 = a * b * (a - c)^2 + b * c * (a - b)^2 + a * c * (b - c)^2 := by
  (intros; linarith)
