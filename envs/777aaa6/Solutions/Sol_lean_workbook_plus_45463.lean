-- Prove2me | solution 1 for lean_workbook_plus_45463
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:10:44.519399+00:00
-- url     : https://prove2.me/submissions/20ab662f-c95e-42fa-ade5-8ae7672c4de6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (p₁ p₂ : ℝ) : p₁ / p₂ + p₂ / p₁ = (p₁ ^ 2 + p₂ ^ 2) / (p₁ * p₂) := by
  intros
  grind
