-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_drawing__p2m_6e5a9dbe_f5b6_4fde_9426_557ef9f6a091_a1
-- name    : WilliamsonShmoys.planar_edge_bound_from_drawing__p2m_6e5a9dbe_f5b6_4fde_9426_557ef9f6a091_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:22:15.329793+00:00
-- url     : https://prove2.me/theorems/da4fb518-365b-4370-9ab7-15c5771178a5
-- title:
--   Simple planar edge bound from a drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a crossing-free drawing, |E| + 6 ≤ 3|V|. Prove by extending the planar graph to a maximal planar graph on the same vertex set, then use Euler’s formula and the fact that each face of a simple maximal planar graph with at least three vertices has boundary length three. The lower bound of three vertices is essential to this edge-bound form: it excludes the one-edge graph on two vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound_from_drawing__p2m_6e5a9dbe_f5b6_4fde_9426_557ef9f6a091_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K) :
    letI : (L : SimpleGraph V) -> DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    K.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
