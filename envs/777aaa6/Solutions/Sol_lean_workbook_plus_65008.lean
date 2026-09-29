-- Prove2me | solution 1 for lean_workbook_plus_65008
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:58:38.208749+00:00
-- url     : https://prove2.me/submissions/86df3598-9eeb-4c5f-a583-60e11f45eb88

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (p m n : ℕ) (hp : p.Prime) (hp1 : p ∣ m + n) (h : m ≡ -n [ZMOD p]) : m^2 ≡ n^2 [ZMOD p] := by
  have hh := h.pow 2
  simpa only [neg_sq,Int.natCast_pow] using hh
