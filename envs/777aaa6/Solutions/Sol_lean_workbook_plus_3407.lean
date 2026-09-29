-- Prove2me | solution 1 for lean_workbook_plus_3407
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:08:28.971995+00:00
-- url     : https://prove2.me/submissions/196e16e0-3bfc-4c75-a95e-1a7c705cf602

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c p q : ℝ)
  (h₀ : a + b + c = p)
  (h₁ : a * b + b * c + c * a = q)
  (h₂ : 8 * (p^2 - 2 * q) * q ≤ p^4) :
  16 * q^2 - 8 * p^2 * q + p^4 ≥ 0 := by
  (intros; linarith)
