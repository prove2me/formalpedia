-- Prove2me | solution 1 for lean_workbook_plus_5635
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:11:54.415731+00:00
-- url     : https://prove2.me/submissions/9f840abb-6125-49ca-9edf-8838d8376fca

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x ai : ℂ) : (x + ai)^7 = (x^7 + 7 * (ai * x^6) + 21 * (ai^2 * x^5) + 35 * (ai^3 * x^4) + 35 * (ai^4 * x^3) + 21 * (ai^5 * x^2) + 7 * (ai^6 * x) + ai^7) ∧ (x - ai)^7 = (x^7 - 7 * (ai * x^6) + 21 * (ai^2 * x^5) - 35 * (ai^3 * x^4) + 35 * (ai^4 * x^3) - 21 * (ai^5 * x^2) + 7 * (ai^6 * x) - ai^7) := by
  intros
  grind
