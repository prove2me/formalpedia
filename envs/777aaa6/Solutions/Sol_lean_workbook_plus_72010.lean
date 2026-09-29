-- Prove2me | solution 1 for lean_workbook_plus_72010
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:27:30.38307+00:00
-- url     : https://prove2.me/submissions/b1a30611-ad57-4aa4-930d-0fbe217f75eb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) : (x = 2018 ∧ y = 2015 ∧ z = 2019.5) ↔ (1/3 * min x y + 2/3 * max x y = 2017 ∧ 1/3 * min y z + 2/3 * max y z = 2018 ∧ 1/3 * min z x + 2/3 * max z x = 2019) := by
  constructor
  · rintro ⟨rfl,rfl,rfl⟩
    norm_num <;> exact ⟨rfl,rfl,rfl⟩
  · rintro ⟨hxy,hyz,hzx⟩
    simp only [min_def,max_def] at hxy hyz hzx
    split_ifs at hxy hyz hzx <;> (refine ⟨?_,?_,?_⟩ <;> linarith)
