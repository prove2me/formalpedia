-- Prove2me | solution 1 for lean_workbook_plus_6188
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:51:05.076113+00:00
-- url     : https://prove2.me/submissions/affed2fa-e3b2-429c-a548-967fe81b1b05

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b : ℤ} (h : a ∣ b) : a ∣ a + b := by
  (intros; simp_all)
