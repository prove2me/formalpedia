-- Prove2me | Theorems.Thm_WorldLine_four_velocity_norm
-- name    : WorldLine.four_velocity_norm
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T02:10:47.291576+00:00
-- url     : https://prove2.me/theorems/1a167f94-581a-495a-a162-e154a728d26b
-- title:
--   The four-velocity is a unit timelike vector
-- statement:
--   **The four-velocity is a unit timelike vector.**
--
--   Let `u` be a timelike separation vector, $\eta(u, u) < 0$, so that $-\eta(u,u) > 0$ and the square root is real and positive. Let `fourVelocity u = u / √(-η(u,u))` — the tangent rescaled by its own Minkowski norm, which is the change of the curve parameter to proper time ("One usually uses the proper time of an object or an observer as the curve parameter $\tau$ along the world line").
--
--   **Conclusion:** the four-velocity has unit Minkowski norm:
--
--   $$\eta(\mathrm{fourVelocity}(u),\ \mathrm{fourVelocity}(u)) \;=\; -1.$$
--
--   In words: parametrizing a worldline by proper time makes its tangent a unit timelike vector — the source's four-velocity $v = (dx^0/d\tau, dx^1/d\tau, dx^2/d\tau, dx^3/d\tau)$, which satisfies $v\cdot v = -1$ in the $(-,+,+,+)$ convention. This normalization is what makes the time component of the four-velocity the energy per unit rest mass (in units $c = 1$).
--
--   **Formalization note.** Scaling computation: $\eta(u/\lambda, u/\lambda) = \eta(u,u)/\lambda^2$ with $\lambda = \sqrt{-\eta(u,u)}$ and $\lambda^2 = -\eta(u,u)$, using that the square root of a positive real squares back to its argument and that division distributes over the components of the Pi type. The hypothesis `hu : IsTimelike u` is exactly what keeps $\lambda$ real and nonzero.
-- source:
--   Wikipedia, World line, https://en.wikipedia.org/wiki/World_line (source of the quoted statements, reproduced verbatim in the definition file) (four-velocity: the tangent vector 'termed four-velocity'; 'One usually uses the proper time of an object or an observer as the curve parameter tau along the world line')

import Mathlib
import Definitions.Def_WorldLine

namespace WorldLine

open Matrix

/-- Milestone: the four-velocity is a unit timelike vector.  Rescaling any
timelike tangent by its own Minkowski norm — which is what switching to proper
time as the curve parameter ("One usually uses the proper time of an object or
an observer as the curve parameter tau along the world line") does to the
tangent — produces a vector of Minkowski norm `-1`: the four-velocity `v` with
`v . v = -1` of the source's four-vector formalism. -/
theorem four_velocity_norm (u : Sp) (hu : IsTimelike u) :
    mink (fourVelocity u) (fourVelocity u) = -1 := by
  sorry

end WorldLine
