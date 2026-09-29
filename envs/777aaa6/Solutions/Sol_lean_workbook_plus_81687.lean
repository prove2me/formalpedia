-- Prove2me | solution 1 for lean_workbook_plus_81687
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:36:39.146415+00:00
-- url     : https://prove2.me/submissions/067def7b-05d9-4789-82a1-01b08a5df0fd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d e f : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e) (hf : 1 ≤ f) (hab : a^2 * b^2 * c^2 * d^2 * e^2 * f^2 = (2 * a - 1) * (2 * b - 1) * (2 * c - 1) * (2 * d - 1) * (2 * e - 1) * (2 * f - 1)) : a + b + c + d + e + f ≥ 6 := by
  (intros; linarith)
