-- Prove2me | solution 1 for lean_workbook_plus_7615
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:00.915906+00:00
-- url     : https://prove2.me/submissions/89a65ecf-7556-4b68-b53d-e1184061ef6f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y k : ℝ)
  (h₀ : x + 1/y = k)
  (h₁ : y ≠ 0)
  (h₂ : k*y - 1 ≠ 0) :
  x = (k*y - 1)/y ∧ 1/x = y/(k*y - 1) := by
  intros
  grind
