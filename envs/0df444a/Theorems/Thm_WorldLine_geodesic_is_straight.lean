-- Prove2me | Theorems.Thm_WorldLine_geodesic_is_straight
-- name    : WorldLine.geodesic_is_straight
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T02:12:04.875805+00:00
-- url     : https://prove2.me/theorems/94ddb136-6b66-4dc0-9dfc-905e02fb54b2
-- title:
--   Geodesics of Minkowski space are straight lines (goal)
-- statement:
--   **Geodesics of Minkowski space are straight lines — the goal theorem.**
--
--   The source: "World lines of freely falling particles/objects are called geodesics. In special relativity these are straight lines in Minkowski space"; and, per Harvey, "If the worldline M is a line segment, then the particle is said to be in free fall."
--
--   Let $\gamma : \mathbb{R} \to Sp$ be a geodesic in the sense of the definition file: twice continuously differentiable, with vanishing coordinate acceleration at every parameter value,
--
--   $$\gamma''(t) \;=\; 0 \quad \text{for all } t,$$
--
--   which is the geodesic equation of flat Minkowski space in inertial coordinates (the Christoffel symbols vanish in these coordinates).
--
--   **Conclusion:** $\gamma$ is affine — there exist fixed events $a, v : Sp$ with
--
--   $$\gamma(t) \;=\; a + t\,v \quad \text{for all } t.$$
--
--   In words: a freely falling particle in Minkowski spacetime traces a straight worldline at constant four-velocity. This is the flat-spacetime content of the geodesic principle — the identification of free fall with the straight-line segments of Harvey's characterization — and the seed of its curved-spacetime generalization (out of scope here).
--
--   **Formalization note.** Componentwise analysis on the Pi type: for each of the four coordinate functions $\gamma^i$ one has $(\gamma^i)'' = 0$, hence $\gamma^i$ has constant derivative (Mathlib's derivative-vanishing-implies-constant machinery, e.g. via the mean-value theorem), and one further integration gives $\gamma^i(t) = a_i + t\,v_i$; reassembling the components gives the affine form. The `ContDiff ℝ 2` half of `IsGeodesic` guarantees the derivatives exist and misbehave nowhere.
-- source:
--   Wikipedia, World line, https://en.wikipedia.org/wiki/World_line (source of the quoted statements, reproduced verbatim in the definition file) ('World lines of freely falling particles/objects are called geodesics. In special relativity these are straight lines in Minkowski space'; Harvey: 'If the worldline M is a line segment, then the particle is said to be in free fall')

import Mathlib
import Definitions.Def_WorldLine

namespace WorldLine

open Matrix

/-- The goal — geodesics of Minkowski space are straight lines: "World lines of
freely falling particles/objects are called geodesics. In special relativity
these are straight lines in Minkowski space"; and per Harvey, "If the worldline
M is a line segment, then the particle is said to be in free fall."  A twice
continuously differentiable worldline in free fall — coordinate acceleration
vanishing at every parameter value, which is the geodesic equation of flat
Minkowski space in inertial coordinates — is affine: `γ t = a + t v` for fixed
events `a, v`. -/
theorem geodesic_is_straight (γ : ℝ → Sp) (hγ : IsGeodesic γ) :
    ∃ a v : Sp, ∀ t : ℝ, γ t = a + t • v := by
  sorry

end WorldLine
