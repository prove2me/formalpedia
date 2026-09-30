-- Prove2me | solution 1 for lean_workbook_plus_77026
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:21:49.167698+00:00
-- url     : https://prove2.me/submissions/12f0108d-0758-42cb-9ed0-5441eff56c2b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution {a b c : ℝ} :
    a*b*c*(a+b+c) ≤ a^2*b^2+b^2*c^2+c^2*a^2 := by
  nlinarith [sq_nonneg (a*b-b*c), sq_nonneg (b*c-c*a), sq_nonneg (c*a-a*b)]
