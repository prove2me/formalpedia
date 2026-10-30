-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_784d1fda_4529_43fd_94a5_bf399d6fa183
-- name    : WilliamsonShmoys.maximal_planar_edge_count_784d1fda_4529_43fd_94a5_bf399d6fa183
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:22:36.434416+00:00
-- url     : https://prove2.me/theorems/85feeb6e-416f-4035-9d68-f9235dbc5e7b
-- title:
--   A maximal planar graph has the triangulation edge count
-- statement:
--   For a graph on at least three vertices satisfying the supplied drawing predicate, maximality among planar supergraphs implies the usual triangulation edge count. The independent route is to establish connectedness and triangular faces from maximality, then apply Euler’s formula and count face-edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_784d1fda_4529_43fd_94a5_bf399d6fa183
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 <= Fintype.card V)
    (hmax : forall R : SimpleGraph V,
      Q.edgeSet ⊆ R.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn R ->
      R.edgeSet = Q.edgeSet) :
    Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
