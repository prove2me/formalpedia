-- Prove2me | solution 1 for lean_workbook_plus_15349
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:57.300588+00:00
-- url     : https://prove2.me/submissions/d85d9495-1098-4802-b9bc-5f1ba3987bc5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : {0, 1, 4, 5, 6, 9} = {n : ℕ | n < 10 ∧ ∃ k : ℕ, k < 10 ∧ n ≡ k ^ 2 [ZMOD 10]} := by
  ext n
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_setOf_eq]
  constructor
  · rintro (rfl|rfl|rfl|rfl|rfl|rfl)
    · exact ⟨by norm_num,0,by norm_num,by norm_num [Int.ModEq]⟩
    · exact ⟨by norm_num,1,by norm_num,by norm_num [Int.ModEq]⟩
    · exact ⟨by norm_num,2,by norm_num,by norm_num [Int.ModEq]⟩
    · exact ⟨by norm_num,5,by norm_num,by norm_num [Int.ModEq]⟩
    · exact ⟨by norm_num,4,by norm_num,by norm_num [Int.ModEq]⟩
    · exact ⟨by norm_num,3,by norm_num,by norm_num [Int.ModEq]⟩
  · rintro ⟨hn,k,hk,h⟩
    interval_cases k <;> norm_num [Int.ModEq] at h <;> omega
