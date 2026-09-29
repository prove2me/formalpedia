-- Prove2me | solution 1 for lean_workbook_plus_52337
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:47.113714+00:00
-- url     : https://prove2.me/submissions/cb8321fd-f76e-4d93-b31d-23b8cb00e257

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (m n p q : ℝ) : (m^2 + n^2)*(p^2 + q^2) ≥ (m * p + n * q)^2 := by
  intros
  have h : (0 : ℝ) ≤ ((m^2 + n^2)*(p^2 + q^2)) - ((m * p + n * q)^2) := by
    calc
      0 ≤ (1 : ℝ) * (((n * p) + ((-1) * m * q)))^2 := by positivity
      _ = ((m^2 + n^2)*(p^2 + q^2)) - ((m * p + n * q)^2) := by ring
  exact sub_nonneg.mp h
