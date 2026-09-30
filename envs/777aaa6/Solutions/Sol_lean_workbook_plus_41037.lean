-- Prove2me | solution 1 for lean_workbook_plus_41037
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:21:12.886995+00:00
-- url     : https://prove2.me/submissions/0a0765cd-7974-4fc4-b94b-198f3efe6439

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) : a^2 * b + b^2 * c + c^2 * a ≤ Real.sqrt ((a^2 + b^2 + c^2)^3 / 3) := by
  have hS : 0 ≤ a^2 + b^2 + c^2 := by positivity
  -- Cauchy–Schwarz (Lagrange identity) with vectors (a,b,c) and (ab,bc,ca)
  have cs : (a^2 * b + b^2 * c + c^2 * a)^2
      ≤ (a^2 + b^2 + c^2) * ((a*b)^2 + (b*c)^2 + (c*a)^2) := by
    nlinarith [sq_nonneg (a*(b*c) - b*(a*b)), sq_nonneg (a*(c*a) - c*(a*b)),
      sq_nonneg (b*(c*a) - c*(b*c))]
  -- 3(a²b²+b²c²+c²a²) ≤ (a²+b²+c²)²
  have q : 3 * ((a*b)^2 + (b*c)^2 + (c*a)^2) ≤ (a^2 + b^2 + c^2)^2 := by
    nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2)]
  have h2 : (a^2 * b + b^2 * c + c^2 * a)^2 ≤ (a^2 + b^2 + c^2)^3 / 3 := by
    have := mul_le_mul_of_nonneg_left q hS
    nlinarith
  calc a^2 * b + b^2 * c + c^2 * a ≤ |a^2 * b + b^2 * c + c^2 * a| := le_abs_self _
    _ ≤ Real.sqrt ((a^2 + b^2 + c^2)^3 / 3) := Real.abs_le_sqrt h2
