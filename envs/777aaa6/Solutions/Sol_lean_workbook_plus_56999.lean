-- Prove2me | solution 1 for lean_workbook_plus_56999
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:53:51.07531+00:00
-- url     : https://prove2.me/submissions/d6ea861b-61a3-40fa-bd37-4888e1a6dad5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {x : ℤ} (hx : x ≡ 0 [ZMOD 3]) : x^2 ≡ 0 [ZMOD 3] := by
  have hh := hx.pow 2
  simpa using hh
