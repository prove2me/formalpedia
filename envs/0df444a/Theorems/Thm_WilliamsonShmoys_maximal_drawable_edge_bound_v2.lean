-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_bound_v2
-- name    : WilliamsonShmoys.maximal_drawable_edge_bound_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:03:07.133738+00:00
-- url     : https://prove2.me/theorems/ef84e714-aa96-448f-8239-07c733b92f0a
-- title:
--   An inclusion-maximal drawable graph has the planar edge bound
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3|V|−6 edges. Prove this by deriving connectedness and triangular faces from maximality of the given drawing, then applying Euler’s formula and counting face-edge incidences. At three vertices, maximality permits the triangle, giving the equality boundary case. This child contains the remaining topological formalization.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_bound_v2
    {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W = U)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by sorry
