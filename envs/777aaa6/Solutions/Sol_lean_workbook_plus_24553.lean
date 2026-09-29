-- Prove2me | solution 1 for lean_workbook_plus_24553
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:03.174315+00:00
-- url     : https://prove2.me/submissions/af582051-e5e6-4dc0-aa16-7f060c0054aa

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a : ℕ → ℝ) (n : ℕ) (h₁ : a (n+1) = (2^(n+1) + 7^(n+1)) * (3^n + 11^n)) (h₂ : a n = (2^n + 7^n) * (3^(n+1) + 11^(n+1))) : a (n+1) / a n = (2^(n+1) + 7^(n+1)) / (2^n + 7^n) * (3^n + 11^n) / (3^(n+1) + 11^(n+1)) := by
  intros
  grind
