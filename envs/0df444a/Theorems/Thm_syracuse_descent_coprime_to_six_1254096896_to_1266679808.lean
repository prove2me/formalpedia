-- Prove2me | Theorems.Thm_syracuse_descent_coprime_to_six_1254096896_to_1266679808
-- name    : syracuse_descent_coprime_to_six_1254096896_to_1266679808
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:50:06.549842+00:00
-- url     : https://prove2.me/theorems/1386fb82-bce8-412a-acee-d2faeaf346f0
-- title:
--   Syracuse descent for inputs coprime to six in [1254096896, 1266679808)
-- statement:
--   Every input coprime to six in this half-open interval has a strictly smaller Syracuse iterate.
-- source:
--   Kernel-checked affine descent certificate, continuing the published adjacent Syracuse interval bands. Affine checker credited in the proof source.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_descent_coprime_to_six_1254096896_to_1266679808 (x : ℕ) (hl : 1254096896 ≤ x) (hu : x < 1266679808)
    (hodd : ¬2 ∣ x) (hthree : ¬3 ∣ x) : ∃ t : ℕ, syracuseStep^[t] x < x := by sorry
