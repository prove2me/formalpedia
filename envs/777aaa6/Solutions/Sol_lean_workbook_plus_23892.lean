-- Prove2me | solution 1 for lean_workbook_plus_23892
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:00.376932+00:00
-- url     : https://prove2.me/submissions/3735b240-e2b9-429d-b9d9-26c66038f4f3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n z : ℂ)
  (h₀ : n = 2)
  (h₁ : z = (-1 + Complex.I) / 2) :
  z^2 + z = (-1 / 2) := by
  rw [h₁]
  ring_nf
  norm_num [Complex.I_sq]
