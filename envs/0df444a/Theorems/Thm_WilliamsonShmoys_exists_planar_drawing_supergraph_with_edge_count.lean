-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_drawing_supergraph_with_edge_count
-- name    : WilliamsonShmoys.exists_planar_drawing_supergraph_with_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:48:51.738349+00:00
-- url     : https://prove2.me/theorems/e394af09-49a8-43e3-a562-53cf2d741322
-- title:
--   Triangulation completion for a drawable graph
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of size at least three extends, on the same vertices, to a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_drawing_supergraph_with_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    ∃ L : SimpleGraph V, K <= L ∧ HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
