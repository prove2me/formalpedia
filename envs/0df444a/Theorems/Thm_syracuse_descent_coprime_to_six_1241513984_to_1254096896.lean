-- Prove2me | Theorems.Thm_syracuse_descent_coprime_to_six_1241513984_to_1254096896
-- name    : syracuse_descent_coprime_to_six_1241513984_to_1254096896
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:50:08.804268+00:00
-- url     : https://prove2.me/theorems/75c3e517-81ac-4f78-bc99-3b504ba022d5
-- title:
--   Syracuse descent for inputs coprime to six in [1241513984, 1254096896)
-- statement:
--   Every input coprime to six in this half-open interval has a strictly smaller Syracuse iterate.
-- source:
--   Kernel-checked affine descent certificate, continuing the published adjacent Syracuse interval bands. Affine checker credited in the proof source.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_descent_coprime_to_six_1241513984_to_1254096896 (x : ℕ) (hl : 1241513984 ≤ x) (hu : x < 1254096896)
    (hodd : ¬2 ∣ x) (hthree : ¬3 ∣ x) : ∃ t : ℕ, syracuseStep^[t] x < x := by sorry
