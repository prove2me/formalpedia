-- Prove2me | solution 1 for lean_workbook_plus_41929
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:13:06.963778+00:00
-- url     : https://prove2.me/submissions/02e346b9-3862-4ee8-b64a-5255cb388df1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (k : ℕ) : (1 + Real.sqrt 5) ^ k / 2 ^ k + (1 + Real.sqrt 5) ^ (k + 1) / 2 ^ (k + 1) = (1 + Real.sqrt 5) ^ (k + 2) / 2 ^ (k + 2) ∧ (1 - Real.sqrt 5) ^ k / 2 ^ k + (1 - Real.sqrt 5) ^ (k + 1) / 2 ^ (k + 1) = (1 - Real.sqrt 5) ^ (k + 2) / 2 ^ (k + 2) := by
  intros
  grind
