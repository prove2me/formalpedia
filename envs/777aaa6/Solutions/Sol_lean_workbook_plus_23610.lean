-- Prove2me | solution 1 for lean_workbook_plus_23610
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:00.361367+00:00
-- url     : https://prove2.me/submissions/54aaae97-dc36-4e37-a23e-99b570ebccc6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {k : ℤ} (h : k ^ 2 ≡ 1 [ZMOD 8]) : Odd k := by
  apply Int.odd_iff.mpr
  have hm : k%8=0 ∨ k%8=1 ∨ k%8=2 ∨ k%8=3 ∨ k%8=4 ∨ k%8=5 ∨ k%8=6 ∨ k%8=7 := by omega
  rcases hm with hm|hm|hm|hm|hm|hm|hm|hm <;> simp [Int.ModEq,pow_two,Int.mul_emod,hm] at h <;> omega
