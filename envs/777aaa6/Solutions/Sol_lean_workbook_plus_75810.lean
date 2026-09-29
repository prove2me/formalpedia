-- Prove2me | solution 1 for lean_workbook_plus_75810
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:40.336648+00:00
-- url     : https://prove2.me/submissions/b4ae8275-0580-4871-a4e1-766d044e1ccc

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : {n : ℕ | n ≡ 4 [ZMOD 6]} = {n : ℕ | 0 < n ∧ n ≡ 4 [ZMOD 6]} := by
  ext n
  change (n:ℤ) ≡ 4 [ZMOD 6] ↔ 0<n ∧ (n:ℤ) ≡ 4 [ZMOD 6]
  constructor
  · intro h
    refine ⟨?_,h⟩
    by_contra hn
    have : n=0 := by omega
    subst n
    norm_num [Int.ModEq] at h
  · exact And.right
