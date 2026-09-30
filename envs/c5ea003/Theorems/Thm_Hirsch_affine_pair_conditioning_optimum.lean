-- Prove2me | Theorems.Thm_Hirsch_affine_pair_conditioning_optimum
-- name    : Hirsch.affine_pair_conditioning_optimum
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-16T18:55:57.116557+00:00
-- url     : https://prove2.me/theorems/b2a9ab62-97c7-44d0-a44f-ef4d0d82d87c
-- title:
--   Exact affine metric barrier for two pairs of facet-normal rays
-- statement:
--   For every real 0<e<1 and every positive definite Gram matrix G=[[X,Z],[Z,Y]], let s_1^2=e^2(XY-Z^2)/(X(X+2eZ+e^2Y)) and s_2^2=e^2(XY-Z^2)/(Y(Y+2eZ+e^2X)). These are the squared sines between a and a+e b, and between b and b+e a, for linearly independent vectors a,b with Gram matrix G. Then min(s_1^2,s_2^2)<=e^2 for EVERY such G, and equality is attained by X=Y=1,Z=-e. Thus choosing an arbitrary invertible affine coordinate change cannot make both pairs better separated than e. The target is this exact algebraic metric optimum. Realization as genuine facets of a simple octagon and higher-dimensional products, the graph-diameter formula, and diagonal gain-graph recognition are separately justified in the accompanying research note, not silently part of the Lean statement.
-- source:
--   Direct Gram identities in research/AFFINE_CONDITIONING_BARRIER.md; conditioning notion from Dadush-Haehnle, arXiv:1412.6705v1 Definition 4. This is a new project interface, not a historical-priority claim or a proof of Polynomial Hirsch.

import Mathlib
set_option autoImplicit false

theorem Hirsch.affine_pair_conditioning_optimum (e : ℝ) (he : 0 < e) (he1 : e < 1) :
    (∀ X Y Z : ℝ, 0 < X → 0 < Y → Z ^ 2 < X * Y →
      min (e ^ 2 * (X * Y - Z ^ 2) /
            (X * (X + 2 * e * Z + e ^ 2 * Y)))
          (e ^ 2 * (X * Y - Z ^ 2) /
            (Y * (Y + 2 * e * Z + e ^ 2 * X))) ≤ e ^ 2) ∧
    ∃ X Y Z : ℝ, 0 < X ∧ 0 < Y ∧ Z ^ 2 < X * Y ∧
      min (e ^ 2 * (X * Y - Z ^ 2) /
            (X * (X + 2 * e * Z + e ^ 2 * Y)))
          (e ^ 2 * (X * Y - Z ^ 2) /
            (Y * (Y + 2 * e * Z + e ^ 2 * X))) = e ^ 2 := by sorry
