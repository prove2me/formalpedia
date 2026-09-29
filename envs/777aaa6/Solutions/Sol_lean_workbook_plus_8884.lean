-- Prove2me | solution 1 for lean_workbook_plus_8884
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:21.178966+00:00
-- url     : https://prove2.me/submissions/ac2ee26d-f9f2-4a3f-8bb9-0edb163bcd1f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) : (a * b + b * c + c * d + d * e + e * a) * (a * c + b * d + e * c + a * d + b * e) - 5 * d * e * c * a - 5 * d * e * a * b - 5 * c * b * d * e - 5 * e * b * c * a - 5 * a * b * c * d = c * e * (a - b) ^ 2 + d * e * (a - c) ^ 2 + b * c * (a - d) ^ 2 + b * d * (a - e) ^ 2 + a * d * (b - c) ^ 2 + a * e * (b - d) ^ 2 + c * d * (b - e) ^ 2 + b * e * (c - d) ^ 2 + a * b * (c - e) ^ 2 + a * c * (d - e) ^ 2 := by
  (intros; linarith)
