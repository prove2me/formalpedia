-- Prove2me | solution 1 for lean_workbook_plus_52521
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:29.906217+00:00
-- url     : https://prove2.me/submissions/93729c26-92a5-4992-8d39-dc3622739f34

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {n : ℤ} (h : n ≡ 1 [ZMOD 4] ∨ n ≡ 3 [ZMOD 4]) : n ^ 2 ≡ 1 [ZMOD 4] := by
  rcases h with h|h
  · have hp := h.pow 2
    norm_num [Int.ModEq] at hp ⊢
    exact hp
  · have hp := h.pow 2
    norm_num [Int.ModEq] at hp ⊢
    exact hp
