-- Prove2me | solution 1 for lean_workbook_plus_51827
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:40:44.036324+00:00
-- url     : https://prove2.me/submissions/7eab6a2a-e47b-4cbb-8ddf-21324bf38695

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a n c : ℕ} (h₁ : a ≡ 1 [ZMOD c]) : a ^ n ≡ 1 [ZMOD c] := by
  simpa only [one_pow] using h₁.pow n
