-- Prove2me | Theorems.Thm_syracuse_descent_coprime_to_six_1266679808_to_1279262720
-- name    : syracuse_descent_coprime_to_six_1266679808_to_1279262720
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:50:05.510709+00:00
-- url     : https://prove2.me/theorems/ed31554c-d975-4755-ba5d-456e4c3f4edd
-- title:
--   Syracuse descent for inputs coprime to six in [1266679808, 1279262720)
-- statement:
--   Every input coprime to six in this half-open interval has a strictly smaller Syracuse iterate.
-- source:
--   Kernel-checked affine descent certificate, continuing the published adjacent Syracuse interval bands. Affine checker credited in the proof source.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_descent_coprime_to_six_1266679808_to_1279262720 (x : ℕ) (hl : 1266679808 ≤ x) (hu : x < 1279262720)
    (hodd : ¬2 ∣ x) (hthree : ¬3 ∣ x) : ∃ t : ℕ, syracuseStep^[t] x < x := by sorry
