-- Prove2me | solution 1 for lean_workbook_plus_23365
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:53:32.134628+00:00
-- url     : https://prove2.me/submissions/b0e23468-8c17-4999-ab18-a48880e592ae

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b : ℕ} (hab : Nat.Coprime a b) : ∃ n, a*n ≡ 1 [ZMOD b] := by
  intros
  exact?
