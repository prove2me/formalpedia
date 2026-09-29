-- Prove2me | solution 1 for lean_workbook_plus_61583
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:31:37.309763+00:00
-- url     : https://prove2.me/submissions/e06d773d-addd-4243-9e72-ce52c755684b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ k : ℕ, (2:ℝ)^k * (2/(k+2)) + (2:ℝ)^(k+1) * (2/(k+3)) - (2:ℝ)^k * (1/(k+1)) - (2:ℝ)^(k+1) * (1/(k+2)) = (2:ℝ)^(k+2) / (k+3) - (2:ℝ)^k / (k+1) := by
  (intros; ring)
