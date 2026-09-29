-- Prove2me | solution 1 for lean_workbook_plus_59792
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:18.060979+00:00
-- url     : https://prove2.me/submissions/912b91e1-0654-49df-a1c1-fb08607ecc00

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : a * b + b * c + c * a ≤ |a| * |b| + |a| * |c| + |b| * |c| := by
  have h1 := le_abs_self (a*b)
  have h2 := le_abs_self (b*c)
  have h3 := le_abs_self (c*a)
  simp only [abs_mul] at h1 h2 h3
  nlinarith only [h1,h2,h3]
