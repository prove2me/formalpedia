-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count_7369a359
-- name    : WilliamsonShmoys.maximal_planar_completion_edge_count_7369a359
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:37:37.198102+00:00
-- url     : https://prove2.me/theorems/d107398d-3b3c-4916-8065-d43a14090b20
-- title:
--   Planar completion with the maximal planar edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices can be extended on the same vertex set to a drawable graph with exactly 3|V|−6 edges. Choose a maximal drawable supergraph among the finitely many supergraphs, then establish its edge count using planar triangulation and Euler’s formula. At three vertices the completion is the triangle; this child supplies the main topological work for the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_completion_edge_count_7369a359
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    exists H : SimpleGraph V,
      K <= H /\
      WilliamsonShmoys.HasPlanarDrawingOn H /\
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
