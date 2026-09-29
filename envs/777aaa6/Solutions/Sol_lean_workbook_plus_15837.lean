-- Prove2me | solution 1 for lean_workbook_plus_15837
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:00.934777+00:00
-- url     : https://prove2.me/submissions/3164f76c-a23e-4eac-8c4f-9a8fc34f1416

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (p q r : ℕ) : p ∣ q * r + q + r → p ∣ p * q + q * r + r * p + p + q + r := by
  intro h
  rcases h with ⟨k,hk⟩
  refine ⟨q+r+1+k,?_⟩
  nlinarith
