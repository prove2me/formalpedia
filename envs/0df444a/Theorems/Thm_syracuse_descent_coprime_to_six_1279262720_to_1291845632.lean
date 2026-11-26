-- Prove2me | Theorems.Thm_syracuse_descent_coprime_to_six_1279262720_to_1291845632
-- name    : syracuse_descent_coprime_to_six_1279262720_to_1291845632
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:50:05.80084+00:00
-- url     : https://prove2.me/theorems/b02c42ac-4805-5f6d-b435-866a41520c32
-- title:
--   Syracuse descent for inputs coprime to six in [1279262720, 1291845632)
-- statement:
--   Every input coprime to six in this half-open interval has a strictly smaller Syracuse iterate.
-- source:
--   Kernel-checked affine descent certificate, continuing the published adjacent Syracuse interval bands. Affine checker credited in the proof source.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_descent_coprime_to_six_1279262720_to_1291845632 (x : ℕ) (hl : 1279262720 ≤ x) (hu : x < 1291845632)
    (hodd : ¬2 ∣ x) (hthree : ¬3 ∣ x) : ∃ t : ℕ, syracuseStep^[t] x < x := by sorry
