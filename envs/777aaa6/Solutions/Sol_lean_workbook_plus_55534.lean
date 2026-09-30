-- Prove2me | solution 1 for lean_workbook_plus_55534
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:40.63367+00:00
-- url     : https://prove2.me/submissions/a1cfecdf-fbc5-46bf-80c8-a4c9363fda59

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (p q : Prop) : p ∨ (p ∧ q) ↔ p := by
  simp_all
