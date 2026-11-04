-- Prove2me | Theorems.Thm_MovingSofa_ForMathlib_antitone_pow_div_factorial_two_mul_add
-- name    : MovingSofa.ForMathlib.antitone_pow_div_factorial_two_mul_add
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-11-04T02:58:36.5819+00:00
-- url     : https://prove2.me/theorems/b781e806-e9ef-4a8b-a83c-26add7743c42
-- title:
--   Factorial quotients are antitone past ratio one
-- statement:
--   Stride-two factorial quotients decrease once the term ratio is at most one; the criterion used for trigonometric Taylor tails.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/SpecificLimits/AlternatingBracket.lean#L17-L35

import Mathlib.Analysis.SpecificLimits.Normed

namespace MovingSofa
namespace ForMathlib

theorem antitone_pow_div_factorial_two_mul_add {x : ℝ} (hx0 : 0 ≤ x) {a : ℕ}
    (hx : x ^ 2 ≤ ((a + 1) * (a + 2) : ℕ)) :
    Antitone fun n : ℕ ↦ x ^ (2 * n + a) / (Nat.factorial (2 * n + a) : ℝ) := by sorry

end ForMathlib
end MovingSofa
