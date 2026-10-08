-- Prove2me | Theorems.Thm_d9NextRevenue_hasDerivWithinAt_parameter
-- name    : d9NextRevenue_hasDerivWithinAt_parameter
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T12:39:44.52276+00:00
-- url     : https://prove2.me/theorems/a79ed6ee-c2c1-4f58-bcf8-2835d7b8a84d
-- title:
--   d9NextRevenue_hasDerivWithinAt_parameter
-- statement:
--   If each fixed nonnegative residual-seat value of a parameterized prefix function has a right derivative D(t) at u, then one fixed branch of the next-revenue recursion transports the corresponding derivative to the selected residual seat. D is the real-valued derivative profile over residual seats.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9NextRevenue
open NestedSeatAlloc.IntPolicy

theorem d9NextRevenue_hasDerivWithinAt_parameter
    (G : ℝ → ℝ → ℝ) (D : ℝ → ℝ) (p x fare s u : ℝ)
    (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hG : ∀ t, 0 ≤ t →
      HasDerivWithinAt (fun v => G v t) (D t) (Set.Ici u) u) :
    HasDerivWithinAt (fun v => d9NextRevenue (G v) p x fare s)
      (if s < p then D s else if s < p + x then D p else D (s - x))
      (Set.Ici u) u := by sorry
