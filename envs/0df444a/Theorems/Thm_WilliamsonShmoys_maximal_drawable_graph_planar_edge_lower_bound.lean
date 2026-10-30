-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_planar_edge_lower_bound
-- name    : WilliamsonShmoys.maximal_drawable_graph_planar_edge_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:53:58.007821+00:00
-- url     : https://prove2.me/theorems/50a3c5c3-d94e-4030-87f1-2cfd5e174f82
-- title:
--   Maximal drawable graphs attain the triangulation lower bound
-- statement:
--   A drawable graph maximal under drawable supergraphs on the same vertex set has at least 3n−6 edges. The intended route is to show maximality forces a connected triangulated embedding, then apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_planar_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hPdraw : HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ Q : SimpleGraph V,
      P ≤ Q → HasPlanarDrawingOn Q → Q = P) :
    3 * Fintype.card V ≤ P.edgeSet.ncard + 6 := by sorry
