-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_Supplement_orbit_moments
-- name    : ZLIPPadding.Padding.Supplement.orbit_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:18:18.062346+00:00
-- url     : https://prove2.me/theorems/c88c9f51-800c-4913-8ec8-6ff8dcc21d80
-- title:
--   Proposition 3.2 — Fourth moments and the full design criterion
-- statement:
--   Let $n\ge2$, let $O\in O(n)$ be any real orthogonal matrix, and let $a\in\mathbb Z^n\setminus\{0\}$. Put $m=\sum_i a_i^2$, $A_4=\sum_i a_i^4$, $\beta_a=(m^2-A_4)/(n(n-1))$ and $\kappa_a=((n+2)A_4-3m^2)/(n(n-1))$. If $Y$ is uniform on the distinct vectors of $O\mathcal B_na$, then
--
--   $$\mathbb E[YY^\top]=\frac mn I,\qquad\mathbb E\langle Y,x\rangle^4=3\beta_a\|x\|^4+\kappa_a\sum_i\langle Oe_i,x\rangle^4\quad(x\in\mathbb R^n).$$
--
--   Moreover, $m^{-1/2}O\mathcal B_na$ is a spherical four-design if and only if $\kappa_a=0$. The design condition tests every polynomial of degree at most four. The result supplies the moment interface for Theorem 3.3, including zero and repeated profile coordinates.
--
--   Differences from the source:
--   - encoding: finite orbit averages and normalized surface measure → Fin n coordinates, distinct-element finite averages and radial-ball surface law with explicit polynomial integrability; reason: these are the same Euclidean objects and all degree-at-most-four tests
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 12 (PDF p. 13), Proposition 3.2

import Definitions.Def_ZLIPPadding_Padding_Supplement_Geometry

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal

theorem orbit_moments (n : ℕ) (hn : 2 ≤ n) (O : RMat n)
    (hO : Orthogonal O) (a : ZVec n) (ha : a ≠ 0) :
    (∀ i j, average (orbit a) (fun z =>
      (rotate O (liftZ z)) i * (rotate O (liftZ z)) j) =
        (normSq a / n) * (if i = j then 1 else 0)) ∧
    (∀ x : EVec n, average (orbit a) (fun z =>
      (inner ℝ (rotate O (liftZ z)) x)^4) =
        3*orbitBeta a*‖x‖^4 + orbitKappa a*axisQuartic O x) ∧
    (SphericalFourDesign O a ↔ orbitKappa a = 0) := by sorry

end ZLIPPadding.Padding.Supplement
