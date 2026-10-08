-- Prove2me | Theorems.Thm_d9NextRevenue_hasDerivWithinAt_parameter_left
-- name    : d9NextRevenue_hasDerivWithinAt_parameter_left
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T12:42:24.785935+00:00
-- url     : https://prove2.me/theorems/3b462970-6af1-440a-be67-f84227447761
-- title:
--   d9NextRevenue_hasDerivWithinAt_parameter_left
-- statement:
--   The left-sided counterpart of parameter transport through one fixed recursion branch: a real-valued derivative profile D for the prefix maps to the derivative at the residual seat selected by the next-revenue branch.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9NextRevenue
open NestedSeatAlloc.IntPolicy

theorem d9NextRevenue_hasDerivWithinAt_parameter_left
    (G : ℝ → ℝ → ℝ) (D : ℝ → ℝ) (p x fare s u : ℝ)
    (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hG : ∀ t, 0 ≤ t →
      HasDerivWithinAt (fun v => G v t) (D t) (Set.Iic u) u) :
    HasDerivWithinAt (fun v => d9NextRevenue (G v) p x fare s)
      (if s < p then D s else if s < p + x then D p else D (s - x))
      (Set.Iic u) u := by sorry
