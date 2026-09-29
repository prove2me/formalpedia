-- Prove2me | solution 1 for lean_workbook_plus_69093
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:18:05.130884+00:00
-- url     : https://prove2.me/submissions/314d69a9-5d53-4165-85b5-6a69e632a1a1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) (h : n > 1) : 10^n ≡ 0 [ZMOD 4] := by
  have hn : 2≤n := by omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hn
  apply Int.modEq_zero_iff_dvd.mpr
  rw [hk,pow_add]
  refine ⟨25*10^k,?_⟩
  ring
