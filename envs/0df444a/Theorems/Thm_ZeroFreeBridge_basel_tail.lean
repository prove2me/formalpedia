-- Prove2me | Theorems.Thm_ZeroFreeBridge_basel_tail
-- name    : ZeroFreeBridge.basel_tail
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:52:40.292659+00:00
-- url     : https://prove2.me/theorems/ffb4a92a-9c89-4bf4-9c07-138c908b220b
-- title:
--   Tail of the Basel series
-- statement:
--   The reciprocal-square tail satisfies
--   $$\sum_{n=0}^{\infty}\frac1{(n+2)^2}=\frac{\pi^2}{6}-1.$$
--   This supplies a concrete bound for the Dirichlet series to the right of the strip.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaLower.lean#L20-L32

import Mathlib
/- PHASE 4 (dVP frontier, ζ boundary growth — LOWER BOUND): a uniform lower bound on |ζ|
   at Re s = 2, the missing lower half of the ζ-growth sphere input.

   The composition `DlvpBoundaryDecomp.norm_logDeriv_le_of_boundary_split` needs, on the sphere,
   `log‖ζ z‖ - log‖ζ c‖ ≤ Aζ`; the upper half is `zeta_sphere_bound`, the lower half is a POSITIVE
   lower bound `‖ζ c‖ ≥ c₀`.  Centering the dVP disk at `Re c = 2` makes this an absolute constant:

     `2 - π²/6 ≤ ‖ζ(s)‖`   for   `2 ≤ Re s`   (and `2 - π²/6 > 0`).

   Proof: `ζ(s) = ∑ₙ 1/(n+1)^s = 1 + T` (Dirichlet series, `n=0` term is `1`); reverse triangle
   `‖ζ‖ ≥ 1 - ‖T‖`; `‖T‖ ≤ ∑ₙ 1/(n+2)^{Re s} ≤ ∑ₙ 1/(n+2)² = π²/6 - 1` (termwise since `Re s ≥ 2`,
   the tail of Basel `hasSum_zeta_two`); so `‖ζ‖ ≥ 1 - (π²/6 - 1) = 2 - π²/6`.  conjecture1_proved = False.
-/


open Complex

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.basel_tail : ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 2) ^ 2 = Real.pi ^ 2 / 6 - 1 := by sorry
