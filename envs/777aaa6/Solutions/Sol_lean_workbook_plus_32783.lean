-- Prove2me | solution 1 for lean_workbook_plus_32783
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:40:17.862309+00:00
-- url     : https://prove2.me/submissions/6a0a4f1b-8462-4e4a-8168-bdfe7a56050f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℤ) (h : n%2 = 1) : ∃ k : ℤ, n ^ 2 = 8*k + 1 ∨ n ^ 2 = 8*k + 7 := by
  have hm : n%8=1 ∨ n%8=3 ∨ n%8=5 ∨ n%8=7 := by omega
  have hs : n^2%8=1 := by
    rcases hm with hm|hm|hm|hm <;> norm_num [pow_two,Int.mul_emod,hm]
  refine ⟨n^2/8,Or.inl ?_⟩
  omega
